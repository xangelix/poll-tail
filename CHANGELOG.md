# Changelog

## v0.1.3

This release focuses on significant internal refactoring to improve code maintainability, reduces allocations in the hot path, and improves safety around file seeking.

### Refactoring & Internal Improvements

* **Code Modularization:** Extracted monolithic logic into focused helper functions including `push_parsed_line`, `update_metadata`, `try_open_file` (validating file types), and `default_line_parser`.
* **State Management:** Simplified the state reset logic and `handle_first_tick` control flow to reduce nesting and improve readability.
* **Test Hygiene:** Cleaned up unused imports in the test suite.

### Performance

* **Allocation Reduction:** Optimized `read_new_lines` to reuse buffers where possible, avoiding unnecessary allocations during steady-state polling.

### Safety

* **Overflow Protection:** Improved arithmetic safety when calculating seek positions in `handle_first_tick` to better handle edge cases with file sizes.

### Documentation

* **Clarification:** Updated the README to clearly distinguish between inspecting the buffer via `lines()` versus consuming it via `drain()`.
* **Comments:** Enhanced internal code comments and docstrings for better maintainability.

## v0.1.2

Adds convenience APIs, small perf/logging tweaks, better docs, and solid tests.

* **Release:** v0.1.2
* **Features:** add `len`, `is_empty`, `clear`, `drain`, and `path` helpers
* **Performance:** make `enforce_max_lines` more efficient
* **Fix (tests):** stop running README examples as doctests
* **Meta:** forbid `unsafe_code`, deny `missing_docs`

