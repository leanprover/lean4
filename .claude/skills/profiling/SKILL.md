---
name: profiling
description: Profile Lean programs with demangled names using samply and Firefox Profiler. Use when the user asks to profile a Lean binary or investigate performance.
allowed-tools: Bash, Read, Glob, Grep
---

# Profiling Lean Programs

Full documentation: `script/PROFILER_README.md`.

## Quick Start

```bash
script/lean_profile.sh ./build/release/stage1/bin/lean some_file.lean
```

Requires `samply` (`cargo install samply`) and `python3`.

## Agent Notes

- The pipeline is interactive (serves to browser at the end). When running non-interactively, run the steps manually instead of using the wrapper script.
- The three steps are: `samply record --save-only`, `symbolicate_profile.py`, then `serve_profile.py`.
- `lean_demangle.py` works standalone as a stdin filter (like `c++filt`) for quick name lookups.
- The `--raw` flag on `lean_demangle.py` gives exact demangled names without postprocessing (keeps `._redArg`, `._lam_0` suffixes as-is).
- Use `PROFILE_KEEP=1` to keep the temp directory for later inspection.
- The demangled profile is a standard Firefox Profiler JSON. Function names live in `threads[i].stringArray`, indexed by `threads[i].funcTable.name`.
