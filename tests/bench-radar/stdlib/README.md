# The `stdlib` benchmark

This benchmark executes a complete build of the stage3 stdlib
and collects global and per-module metrics.

The following metrics are collected by a wrapper around the entire build process:

- `stdlib//instructions`
- `stdlib//maxrss`
- `stdlib//task-clock`
- `stdlib//wall-clock`

The following metrics are collected from `leanc --profile` and summed across all modules:

- `stdlib/profile/<name>//wall-clock`

The following metrics are collected from `lakeprof report`:

- `stdlib/lakeprof/longest build path//wall-clock`
- `stdlib/lakeprof/longest rebuild path//wall-clock`

The following metrics are collected individually for each module:

- `stdlib/module/<name>//lines`
- `stdlib/module/<name>//instructions`

If the file `stdlib_upload_lakeprof_report` is present in the repo root,
the lakeprof report will be uploaded once the benchmark run concludes.
