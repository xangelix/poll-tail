#![cfg_attr(not(doctest), doc = include_str!("../README.md"))]
#![forbid(unsafe_code)]
#![deny(missing_docs)]

use std::{
    collections::VecDeque,
    fs::{File, Metadata},
    io::{self, BufRead, BufReader, Seek, SeekFrom},
    path::{Path, PathBuf},
};

use chrono::{DateTime, Utc};
use thiserror::Error;

/// A convenient `Result` type for the poll-tail crate.
pub type Result<T> = std::result::Result<T, Error>;

/// The error type for operations within the poll-tail crate.
#[derive(Error, Debug)]
pub enum Error {
    /// An error occurred during a file I/O operation.
    #[error("I/O error while handling file: {0}")]
    Io(#[from] io::Error),

    /// The specified path exists but is a directory, not a file.
    #[error("The path exists but is not a file: {0:?}")]
    PathIsNotAFile(PathBuf),

    /// An unexpected internal state was reached, indicating a logic bug.
    #[error("Internal state error: {0}")]
    InternalState(&'static str),
}

/// A type alias for the line parsing function.
///
/// The function receives the `String` line and the `Option<DateTime<Utc>>` of the
/// previously parsed line, returning a `(DateTime<Utc>, String)` tuple.
pub type LineParser =
    Box<dyn Fn(String, Option<DateTime<Utc>>) -> (DateTime<Utc>, String) + Send + Sync>;

/// Builds a `FileListener`.
pub struct FileListenerBuilder {
    path: PathBuf,
    max_lines: Option<usize>,
    initial_read_lines: Option<usize>,
    parser: Option<LineParser>,
}

impl FileListenerBuilder {
    /// Creates a new `FileListenerBuilder` for the specified file path.
    pub fn new<P: AsRef<Path>>(path: P) -> Self {
        Self {
            path: path.as_ref().to_path_buf(),
            max_lines: None,
            initial_read_lines: None,
            parser: None,
        }
    }

    /// Sets the maximum number of lines the `FileListener` will keep in its buffer.
    #[must_use]
    pub const fn max_lines(mut self, max: usize) -> Self {
        self.max_lines = Some(max);
        self
    }

    /// Sets the number of lines to read from the end of the file on the first `tick()`.
    #[must_use]
    pub const fn initial_read_lines(mut self, lines: usize) -> Self {
        self.initial_read_lines = Some(lines);
        self
    }

    /// Sets a custom line parser.
    ///
    /// The parser is a closure that takes the read line (`String`) and the timestamp
    /// of the previous line (`Option<DateTime<Utc>>`), and returns a tuple of
    /// `(DateTime<Utc>, String)`. This allows for flexible parsing of custom
    /// timestamp formats or assigning timestamps based on other logic.
    ///
    /// If not set, a default parser is used which looks for an RFC 3339 timestamp
    /// at the beginning of the line.
    #[must_use]
    pub fn parser<F>(mut self, parser: F) -> Self
    where
        F: Fn(String, Option<DateTime<Utc>>) -> (DateTime<Utc>, String) + Send + Sync + 'static,
    {
        self.parser = Some(Box::new(parser));
        self
    }

    /// Constructs the `FileListener`.
    ///
    /// # Errors
    ///
    /// Returns an `Error` if the path exists but is not a regular file, or if
    /// there are permission issues.
    pub fn build(self) -> Result<FileListener> {
        let default_parser = Box::new(|line: String, last_timestamp: Option<DateTime<Utc>>| {
            let mut parts = line.splitn(2, char::is_whitespace);
            let first_word = parts.next().unwrap_or("");

            DateTime::parse_from_rfc3339(first_word).map_or_else(
                |_| (last_timestamp.unwrap_or_else(Utc::now), line.clone()),
                |dt| {
                    (
                        dt.with_timezone(&Utc),
                        parts.next().unwrap_or("").to_string(),
                    )
                },
            )
        });

        let mut listener = FileListener {
            path: self.path,
            reader: None,
            last_metadata: None,
            buffer: VecDeque::new(),
            max_lines: self.max_lines,
            initial_read_lines: self.initial_read_lines,
            is_first_tick: true,
            parser: self.parser.unwrap_or(default_parser),
        };

        match File::open(&listener.path) {
            Ok(file) => {
                let metadata = file.metadata()?;
                if !metadata.is_file() {
                    return Err(Error::PathIsNotAFile(listener.path));
                }
                listener.reader = Some(BufReader::new(file));
                listener.last_metadata = Some(metadata);
            }
            Err(e) if e.kind() == io::ErrorKind::NotFound => {}
            Err(e) => return Err(e.into()),
        }

        Ok(listener)
    }
}

/// A listener that monitors a file for changes and captures new lines.
pub struct FileListener {
    path: PathBuf,
    reader: Option<BufReader<File>>,
    last_metadata: Option<Metadata>,
    buffer: VecDeque<(DateTime<Utc>, String)>,
    max_lines: Option<usize>,
    initial_read_lines: Option<usize>,
    is_first_tick: bool,
    parser: LineParser,
}

impl FileListener {
    /// Creates a new `FileListenerBuilder` for the given file path.
    pub fn builder<P: AsRef<Path>>(path: P) -> FileListenerBuilder {
        FileListenerBuilder::new(path)
    }

    /// Checks the file for changes and updates the internal line buffer.
    ///
    /// # Errors
    ///
    /// Returns an `Error` if filesystem operations fail.
    pub fn tick(&mut self) -> Result<()> {
        if self.reader.is_none() {
            match File::open(&self.path) {
                Ok(file) => {
                    let metadata = file.metadata()?;
                    if !metadata.is_file() {
                        return Err(Error::PathIsNotAFile(self.path.clone()));
                    }
                    self.reader = Some(BufReader::new(file));
                    self.last_metadata = Some(metadata);
                }
                Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(()),
                Err(e) => return Err(e.into()),
            }
        }

        if self.is_first_tick {
            self.is_first_tick = false;
            return self.handle_first_tick();
        }

        match std::fs::metadata(&self.path) {
            Ok(current_metadata) => self.handle_subsequent_tick(current_metadata),
            Err(e) if e.kind() == io::ErrorKind::NotFound => {
                self.reader = None;
                self.last_metadata = None;
                self.buffer.clear();
                self.is_first_tick = true;
                Ok(())
            }
            Err(e) => Err(e.into()),
        }
    }

    /// Returns an immutable reference to the internal buffer of lines.
    #[must_use]
    pub const fn lines(&self) -> &VecDeque<(DateTime<Utc>, String)> {
        &self.buffer
    }

    /// Handles the initial read logic.
    fn handle_first_tick(&mut self) -> Result<()> {
        const AVG_LINE_LEN: u64 = 200;

        if let Some(n_lines) = self.initial_read_lines.filter(|&n| n > 0) {
            // Scope the mutable borrow of the reader to just this block for backfilling.
            let reader = self
                .reader
                .as_mut()
                .ok_or(Error::InternalState("Reader missing during first tick"))?;

            let buffer_size = std::cmp::max(8192, AVG_LINE_LEN * n_lines as u64 * 2);

            let file_len = reader.get_ref().metadata()?.len();
            let seek_pos = file_len.saturating_sub(buffer_size);
            reader.seek(SeekFrom::Start(seek_pos))?;

            if seek_pos > 0 {
                let mut discard = String::new();
                reader.read_line(&mut discard)?;
            }

            let lines: Vec<String> = reader.lines().collect::<io::Result<_>>()?;

            for line in lines.into_iter().rev().take(n_lines).rev() {
                let last_timestamp = self.buffer.back().map(|(ts, _)| *ts);
                self.buffer.push_back((self.parser)(line, last_timestamp));
            }
        } else {
            // If not backfilling, read the entire file from the current position (start).
            self.read_new_lines()?;
        }

        // After reading, update the metadata to reflect the state we've processed.
        let metadata = self
            .reader
            .as_ref()
            .ok_or(Error::InternalState("Reader is missing after initial read"))?
            .get_ref()
            .metadata()?;
        self.last_metadata = Some(metadata);

        Ok(())
    }

    /// Handles change detection on subsequent ticks.
    fn handle_subsequent_tick(&mut self, current_metadata: Metadata) -> Result<()> {
        let last_metadata = self
            .last_metadata
            .as_ref()
            .ok_or(Error::InternalState("Metadata missing on subsequent tick"))?;

        let last_size = last_metadata.len();
        let current_size = current_metadata.len();

        let was_truncated = current_size < last_size;
        let was_modified_in_place = {
            let last_mtime = last_metadata.modified()?;
            let current_mtime = current_metadata.modified()?;
            current_size == last_size && current_mtime > last_mtime
        };

        if was_truncated || was_modified_in_place {
            self.buffer.clear();
            let reader = self
                .reader
                .as_mut()
                .ok_or(Error::InternalState("Reader missing on truncation"))?;
            reader.seek(SeekFrom::Start(0))?;
            self.read_new_lines()?;
        } else if current_size > last_size {
            self.read_new_lines()?;
        }

        self.last_metadata = Some(current_metadata);
        Ok(())
    }

    /// Reads all available lines from the reader's current position.
    fn read_new_lines(&mut self) -> Result<()> {
        let reader = self
            .reader
            .as_mut()
            .ok_or(Error::InternalState("Reader missing for reading new lines"))?;

        let mut line_buf = String::new();
        while reader.read_line(&mut line_buf)? > 0 {
            let last_timestamp = self.buffer.back().map(|(ts, _)| *ts);
            self.buffer
                .push_back((self.parser)(line_buf.clone(), last_timestamp));
            line_buf.clear();
        }
        self.enforce_max_lines();
        Ok(())
    }

    /// Enforces the `max_lines` limit on the buffer.
    fn enforce_max_lines(&mut self) {
        if let Some(max) = self.max_lines {
            while self.buffer.len() > max {
                self.buffer.pop_front();
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{io::Write, thread::sleep, time::Duration};

    use tempfile::NamedTempFile;

    use super::*;

    fn write_to_file(file: &mut File, content: &str) {
        file.write_all(content.as_bytes()).unwrap();
        file.flush().unwrap();
        // Give a moment for the filesystem mtime to update reliably
        sleep(Duration::from_millis(15));
    }

    #[test]
    fn test_file_creation_and_append() -> Result<()> {
        let temp_file = NamedTempFile::new().unwrap();
        let path = temp_file.path().to_path_buf();
        let file = temp_file.reopen().unwrap();

        // Initially, delete the file to test creation detection
        drop(file);
        std::fs::remove_file(&path).unwrap();

        let mut listener = FileListener::builder(&path).build()?;
        listener.tick()?;
        assert!(listener.lines().is_empty());

        // Create the file and write to it
        let mut file = File::create(&path).unwrap();
        write_to_file(&mut file, "line 1\n");
        listener.tick()?;
        assert_eq!(listener.lines().len(), 1);
        assert!(listener.lines()[0].1.contains("line 1"));

        // Append more lines
        write_to_file(&mut file, "line 2\nline 3\n");
        listener.tick()?;
        assert_eq!(listener.lines().len(), 3);
        assert!(listener.lines()[1].1.contains("line 2"));
        assert!(listener.lines()[2].1.contains("line 3"));

        Ok(())
    }

    #[test]
    fn test_initial_read_lines() -> Result<()> {
        let mut temp_file = NamedTempFile::new().unwrap();
        write_to_file(
            temp_file.as_file_mut(),
            "line 1\nline 2\nline 3\nline 4\nline 5\n",
        );

        let mut listener = FileListener::builder(temp_file.path())
            .initial_read_lines(3)
            .build()?;

        // The first tick should backfill the last 3 lines
        listener.tick()?;
        assert_eq!(listener.lines().len(), 3);
        assert!(listener.lines()[0].1.contains("line 3"));
        assert!(listener.lines()[1].1.contains("line 4"));
        assert!(listener.lines()[2].1.contains("line 5"));

        // A subsequent write and tick should just append
        write_to_file(temp_file.as_file_mut(), "line 6\n");
        listener.tick()?;
        assert_eq!(listener.lines().len(), 4);
        assert!(listener.lines()[3].1.contains("line 6"));

        Ok(())
    }

    #[test]
    fn test_max_lines_enforced() -> Result<()> {
        let mut temp_file = NamedTempFile::new().unwrap();
        let mut listener = FileListener::builder(temp_file.path())
            .max_lines(3)
            .build()?;

        write_to_file(
            temp_file.as_file_mut(),
            "line 1\nline 2\nline 3\nline 4\nline 5\n",
        );

        listener.tick()?;
        assert_eq!(listener.lines().len(), 3);
        assert!(listener.lines()[0].1.contains("line 3"));
        assert!(listener.lines()[1].1.contains("line 4"));
        assert!(listener.lines()[2].1.contains("line 5"));

        Ok(())
    }

    #[test]
    fn test_truncation() -> Result<()> {
        let mut temp_file = NamedTempFile::new().unwrap();
        write_to_file(temp_file.as_file_mut(), "line 1\nline 2\n");

        let mut listener = FileListener::builder(temp_file.path()).build()?;
        listener.tick()?;
        assert_eq!(listener.lines().len(), 2);

        // Truncate the file by reopening in create mode
        let mut file = File::create(temp_file.path()).unwrap();
        write_to_file(&mut file, "new line A\n");

        listener.tick()?;
        assert_eq!(listener.lines().len(), 1);
        assert!(listener.lines()[0].1.contains("new line A"));

        Ok(())
    }

    #[test]
    fn test_delete_and_recreate() -> Result<()> {
        let temp_file = NamedTempFile::new().unwrap();
        let path = temp_file.path().to_path_buf();
        let mut file = temp_file.reopen().unwrap();
        write_to_file(&mut file, "initial line\n");

        let mut listener = FileListener::builder(&path)
            .initial_read_lines(10)
            .build()?;
        listener.tick()?;
        assert_eq!(listener.lines().len(), 1);

        // Delete the file
        drop(file);
        std::fs::remove_file(&path).unwrap();
        sleep(Duration::from_millis(15)); // Filesystem grace period

        listener.tick()?;
        assert!(listener.lines().is_empty());
        assert!(listener.reader.is_none()); // State should be reset

        // Recreate and write
        let mut file = File::create(&path).unwrap();
        write_to_file(&mut file, "recreated line 1\nrecreated line 2\n");

        listener.tick()?;
        // The `is_first_tick` logic should re-trigger, reading the whole file
        assert_eq!(listener.lines().len(), 2);
        assert!(listener.lines()[0].1.contains("recreated line 1"));

        Ok(())
    }

    #[test]
    fn test_default_timestamp_parser() -> Result<()> {
        let now_str = Utc::now().to_rfc3339();
        let mut temp_file = NamedTempFile::new().unwrap();
        let line_with_ts = format!("{now_str} my log message\n");
        write_to_file(temp_file.as_file_mut(), &line_with_ts);

        let mut listener = FileListener::builder(temp_file.path()).build()?;
        listener.tick()?;

        assert_eq!(listener.lines().len(), 1);
        // The parser should have stripped the timestamp and returned the rest of the line.
        assert_eq!(listener.lines()[0].1.trim(), "my log message");
        // And the parsed timestamp should be very close to the one we wrote.
        let parsed_ts = listener.lines()[0].0;
        let original_ts = DateTime::parse_from_rfc3339(&now_str).unwrap();
        assert_eq!(parsed_ts, original_ts.with_timezone(&Utc));

        Ok(())
    }

    #[test]
    fn test_custom_parser() -> Result<()> {
        let mut temp_file = NamedTempFile::new().unwrap();
        write_to_file(temp_file.as_file_mut(), "some log line\n");

        let custom_parser = |line: String, _: Option<DateTime<Utc>>| {
            let fake_ts = DateTime::parse_from_rfc3339("2000-01-01T00:00:00Z")
                .unwrap()
                .with_timezone(&Utc);
            (fake_ts, format!("PARSED: {line}"))
        };

        let mut listener = FileListener::builder(temp_file.path())
            .parser(custom_parser)
            .build()?;
        listener.tick()?;

        assert_eq!(listener.lines().len(), 1);
        let (ts, line) = &listener.lines()[0];
        assert_eq!(ts.to_rfc3339(), "2000-01-01T00:00:00+00:00");
        assert!(line.starts_with("PARSED: "));
        assert!(line.contains("some log line"));

        Ok(())
    }

    #[test]
    fn test_timestamp_fallback() -> Result<()> {
        let mut temp_file = NamedTempFile::new().unwrap();
        write_to_file(
            temp_file.as_file_mut(),
            "line with no timestamp\nand another one\n",
        );

        let mut listener = FileListener::builder(temp_file.path()).build()?;
        listener.tick()?;

        assert_eq!(listener.lines().len(), 2);
        let ts1 = listener.lines()[0].0;
        let ts2 = listener.lines()[1].0;

        // The second line should inherit the timestamp from the first, as it also has no timestamp.
        assert_eq!(ts1, ts2);

        Ok(())
    }
}
