# The `build` benchmark

This benchmark executes a complete build of the stage3 stdlib
and collects global and per-module metrics.

The following metrics are collected by a wrapper around the entire build process:

- `build//cycles`
- `build//instructions`
- `build//maxrss`
- `build//task-clock`
- `build//wall-clock`

The following metrics are collected from `leanc --profile` and `leanc --stat` and summed across all modules:

- `build/profile/<name>//wall-clock`
- `build/stat/<name>//amount`
- `build/stat/<name>//bytes`

The following metrics are collected from `lakeprof report`:

- `build/lakeprof/longest build path//wall-clock`
- `build/lakeprof/longest rebuild path//wall-clock`

The following metrics are collected individually for each module:

- `build/module/<name>//lines`
- `build/module/<name>//cycles`
- `build/module/<name>//instructions`
- `build/module/<name>//bytes .ilean`
- `build/module/<name>//bytes .olean`
- `build/module/<name>//bytes .olean.server`
- `build/module/<name>//bytes .olean.private`

If the file `build_upload_lakeprof_report` is present in the repo root,
the lakeprof report will be uploaded once the benchmark run concludes.
