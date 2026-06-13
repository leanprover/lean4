# M2 Final Mission Sweep

This document records the final hygiene sweep for the Lean 4 Zig-backend
mission after all M2 features landed.

## Final state

- **Outer lean4 repo status**: clean outside `.gitignore` and `zig-backend/`
- **Orphan mission processes**: none found
- **`zig-backend/` footprint**: `315M` total (`<= 2 GB` target satisfied)
- **Clean rebuild**: passes from `rm -rf zig-out .zig-cache`
- **Combined symbol check**: passes with `Missing symbols: 0`

## Key paths

| Path | Purpose |
| --- | --- |
| `/Users/davirian/dev/active/lean4/build/release/stage1/bin/lean` | Baseline Lean binary used for smoke tests |
| `/Users/davirian/dev/active/lean4/zig-backend/zig-out/lib/libleanrt-zig.a` | Zig-owned runtime archive |
| `/Users/davirian/dev/active/lean4/zig-backend/zig-out/lib/libleanrt_cpp_partial.a` | Delegated C++ runtime archive |
| `/Users/davirian/dev/active/lean4/zig-backend/tools/check-symbols.sh` | Combined split-runtime symbol checker |
| `/Users/davirian/dev/active/lean4/zig-backend/tests/lean-smoke/run.sh` | End-to-end Lean → C → split-runtime smoke test |
| `/Users/davirian/dev/active/lean4/zig-backend/docs/m2-poc-report.md` | Detailed M2 PoC report |
| `/Users/davirian/dev/active/lean4/zig-backend/docs/baseline.md` | Baseline Lean build record |

## Size snapshot

Measured after the final clean rebuild:

| Path | Size |
| --- | --- |
| `zig-backend/` | `315M` |
| `zig-backend/sync/` | `104M` |
| `zig-backend/.zig-cache/` | `186M` |
| `zig-backend/zig-out/` | `6.7M` |
| `zig-backend/docs/` | `48K` |

Archive sizes:

| Archive | Size |
| --- | --- |
| `zig-out/lib/libleanrt-zig.a` | `3,194,680` bytes |
| `zig-out/lib/libleanrt-zig-testabi.a` | `3,229,092` bytes |
| `zig-out/lib/libleanrt_cpp_partial.a` | `545,600` bytes |

## Symbol-split rationale

After `M2-F10`, the public runtime surface is intentionally split across two
archives:

1. `libleanrt-zig.a` exports the Zig-owned subset implemented during M2.
2. `libleanrt_cpp_partial.a` exports the delegated upstream C++ remainder.

The old monolithic `tools/check-symbols.sh` only inspected
`libleanrt-zig.a`, so it falsely reported delegated symbols as missing.

The updated checker now:

1. Parses one-line `LEAN_EXPORT ... lean_*` declarations from `src/include/lean/lean.h`.
2. Unions the public `lean_*` symbols from both split archives.
3. Uses the upstream monolithic `build/release/stage1/lib/lean/libleanrt.a`
   as a reference to exclude header declarations that are *not* part of the
   archive-level runtime surface on this platform.

Current checker output:

- `lean.h LEAN_EXPORT declarations`: `209`
- `Runtime-required header symbols`: `180`
- `Excluded non-archive declarations`: `29`
- `Missing symbols`: `0`

The 29 exclusions match the upstream monolithic runtime exactly. They fall into
three buckets:

- optional allocator hooks not exported in this build (`lean_alloc_small`,
  `lean_free_small`, `lean_small_mem_size`)
- Lean-defined IO error constructors declared in `lean.h` but not provided by
  the runtime archive
- `lean_st_ref_reset`, likewise declared in `lean.h` but not exported from the
  monolithic runtime archive

## Reproduce from clean

From a clean `zig-backend/` build state:

```bash
cd /Users/davirian/dev/active/lean4/zig-backend
rm -rf zig-out .zig-cache
zig build
./tools/check-symbols.sh
zig build test
zig build test-abi
./tests/lean-smoke/run.sh
```

Expected outcomes:

- `zig build` recreates both split runtime archives under `zig-out/lib/`
- `./tools/check-symbols.sh` exits `0` and prints `Missing symbols: 0`
- `zig build test-abi` exits `0`
- `./tests/lean-smoke/run.sh` prints `Hello, world!`

## Hygiene checks used for mission closure

```bash
git -C /Users/davirian/dev/active/lean4 status --porcelain -- ':!.gitignore' ':!zig-backend' ':!zig-backend/'
ps -ax -o pid=,command= | grep -E 'zig build|scan-commits|replay.py|tests/lean-smoke|test-abi|check-symbols\.sh' | grep -v grep
du -sh /Users/davirian/dev/active/lean4/zig-backend
```

Observed final state:

- outer repo status command printed nothing
- orphan-process check printed nothing
- `du -sh` reported `315M /Users/davirian/dev/active/lean4/zig-backend`

## M3 ordering preference (orchestrator handoff note)

The user (mission orchestrator) has specified that when M3 is launched, the
allocator re-claim work (re-export lean_alloc_object / lean_free_object /
lean_inc_heartbeat / lean_alloc_small / lean_free_small / lean_small_mem_size
from libleanrt-zig.a and remove the M2-F11b carve-out) should run FIRST as
M3-C, BEFORE the not-yet IO error constructors (M3-A) or the low-risk
delegated families (M3-B: floats, once_cold, dbg, st_ref, name/slice).

Rationale: the allocator-ownership story is the riskiest piece of M3 and is
a precondition for M4 (bignums) and M5 (IO/tasks) which will both stress the
allocator path. Surfacing any new allocator regressions early de-risks the
entire remaining roadmap. M3-A and M3-B have no ordering dependency between
themselves and can run in either order after M3-C.
