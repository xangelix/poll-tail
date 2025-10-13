# poll-tail

[![Crates.io](https://img.shields.io/crates/v/poll-tail.svg)](https://crates.io/crates/poll-tail)
[![Docs.rs](https://docs.rs/poll-tail/badge.svg)](https://docs.rs/poll-tail)

A simple, polling-based file tailer that gracefully handles log rotation.

`poll-tail` provides a `FileListener` that monitors a file for changes, similar to `tail --follow`. It's designed to be robust against file truncation, replacement, and deletion, which are common with log rotation mechanisms.

It operates on a synchronous, polling basis via the `tick()` method, making it extremely easy to integrate into any application loop without needing an `async` runtime or complex event-driven dependencies.

## Key Features

- **Simple Polling API**: Just call `tick()` periodically in your loop.
- **Log Rotation Handling**: Seamlessly handles file truncation, deletion, and recreation.
- **Backfilling**: Can be configured to read the last N lines of a file when it first appears.
- **Customizable Parser**: Provides a default RFC 3339 timestamp parser but allows you to supply your own logic for parsing lines.
- **No Async**: Purely synchronous, making it perfect for simple clients, tools, or existing application loops.

## Installation

Add the following to your `Cargo.toml`:

```toml
[dependencies]
poll-tail = "0.1.0" # use the latest version
```

## Usage

Here's a basic example that follows a log file and prints new lines as they appear.

```rust
use std::{time::Duration, thread};

use poll_tail::{FileListener, Error};

fn main() -> Result<(), Error> {
    let log_path = "/var/log/app.log";

    // The builder will succeed even if the log file doesn't exist yet.
    let mut listener = FileListener::builder(log_path)
        .max_lines(1000) // Keep a rolling buffer of the last 1000 lines.
        .initial_read_lines(50) // On first detection, read the last 50 lines.
        .build()?;

    println!("Watching for changes in {log_path}...");

    loop {
        // The core of the library: check the file for changes.
        listener.tick()?;

        // The lines() method gives you access to the internal buffer.
        // You would typically process these lines (e.g., send them, display them)
        // and then clear your own state.
        for (timestamp, line) in listener.lines() {
            // The default parser extracts RFC 3339 timestamps or uses the
            // last known timestamp as a fallback.
            println!("[{}] {}", timestamp.to_rfc3339(), line.trim_end());
        }

        // Poll every second.
        thread::sleep(Duration::from_secs(1));
    }
}
```

## API Overview

- `FileListener`: The main struct that holds the file state and line buffer.
- `FileListenerBuilder`: A convenient builder for configuring the listener.
- `tick()`: The primary method you call to check for file updates.
- `lines()`: Returns a reference to the internal `VecDeque` of `(DateTime<Utc>, String)` tuples.
- `Error`: A `thiserror`-based enum for all possible failures.

## License

This project is licensed under the MIT license.
