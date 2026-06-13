# Mission Strategy — Rewrite Lean 4 Backend in Zig (M1 + M2)

This document describes the high-level strategy, workflows, and conventions for the M1 + M2 mission.

## 1. Commit Replay Workflow

The Lean 4 backend evolved across ~26,441 commits from `0556412f8d` (2018-05-14, "add `runtime` folder") to `master`. Rather than attempting a big-bang rewrite, we use a **commit-by-commit replay** approach:

1. **Scan** — `tools/scan-commits.py` walks the full history and classifies each commit as backend-touching or not. A commit is backend-touching if any changed file falls under:
   - `src/runtime/`
   - `src/Lean/Compiler/IR/`
   - `src/Lean/Compiler/LCNF/`
   - `src/include/lean/`
   - `src/shell/`
   - `src/Init/`
   - `src/library/compiler/` (pre-2020 path)

2. **Report** — For every commit, a JSON report is emitted to `sync/reports/<short-sha>.json` containing:
   - `sha`, `short_sha`, `subject`, `author`, `date`
   - `needs_port` (bool)
   - `backend_changes` (array of `{path, status, zig_target}`)
   - `zig_target` (mapping from C++ path to proposed Zig path)

3. **Replay** — `tools/replay.py <sha>` inspects the backend files at that commit (read-only via `git show`), computes the diff against the previous backend-touching commit, and emits a markdown summary at `replays/<short-sha>.md`. This tells us exactly what would need to be translated if we were replaying history commit-by-commit.

4. **Manifest** — `sync/manifest.json` aggregates the scan with counts per year, per subsystem, total commits, backend-touching commits, and a content hash for reproducibility.

The replay workflow is purely analytical in M1. In M3+ it may drive actual incremental porting.

## 2. ABI Preservation Rule

The C ABI contract is `src/include/lean/lean.h`. Every line of Lean-emitted C references symbols from this header. The Zig runtime must be a drop-in replacement:

- **Struct layouts** must be bit-identical. Zig `extern struct` definitions must match C `struct` definitions field-for-field, with identical `sizeof` and `offsetof` for every documented field. This is enforced by `_Static_assert` in `tests/abi-smoke/layout.c`.
- **Symbol surface** must be complete. Every `LEAN_EXPORT` symbol in `lean.h` must appear in `libleanrt-zig.a` with matching name and `callconv(.c)`. Verified by `tools/check-symbols.sh`.
- **Semantics** must match. Reference counting behavior (ST / MT / persistent), ownership conventions (`lean_obj_arg`, `b_lean_obj_arg`, `u_lean_obj_arg`), and observable side effects must be identical.
- **Header compatibility** — `lean.h` itself is never modified. C consumers (including `stage0/*.c`) continue to `#include <lean/lean.h>` and link against the Zig static library.

If a struct or symbol cannot be reproduced exactly in Zig 0.16, that is a mission blocker. Do not workaround by modifying `lean.h`.

## 3. M2 PoC Plan Summary

M2 proves the ABI-compatible approach works end-to-end on a real Lean-emitted program. The plan:

1. **Object model** (`src/runtime/object.zig`) — `lean_object` header and all per-tag struct variants. Tag constants. `lean_box` / `lean_unbox` / `lean_is_scalar`.
2. **Reference counting** (`src/runtime/rc.zig`) — `lean_inc`, `lean_dec`, `lean_mark_mt`, `lean_mark_persistent`, `lean_is_exclusive`, `lean_is_shared`. ST (positive RC), MT (negative RC with atomics), persistent (RC == 0).
3. **Allocator** (`src/runtime/alloc.zig`) — Small-object thread-local page heap. `LEAN_PAGE_SIZE = 8192`, `LEAN_SEGMENT_SIZE = 8MB`, `LEAN_MAX_SMALL_OBJECT_SIZE = 4096`. Large-object malloc fallback. Heartbeat counter.
4. **Apply / closures** (`src/runtime/apply.zig`) — `lean_apply_1..16`, `lean_apply_n`, `lean_apply_m`, `lean_alloc_closure`. Exact-, under-, and over-arity application.
5. **Box / unbox** (`src/runtime/box.zig`) — Scalar boxing for `usize`, `u32`, `u64`, `float`, `float32`. Round-trip preservation.
6. **Ctor accessors** (`src/runtime/ctor.zig`) — `lean_ctor_get/set`, scalar field accessors (`uint8/16/32/64`, `usize`, `float`, `float32`), `lean_ctor_set_tag`.
7. **Strings + UTF-8** (`src/runtime/string.zig`, `utf8.zig`) — `lean_mk_string`, length, equality, UTF-8 iteration.
8. **Arrays + sarray** (`src/runtime/array.zig`) — Object arrays, byte arrays, float arrays. Push, get, set.
9. **IO panic + init** (`src/runtime/io_min.zig`, `init.zig`) — `lean_panic`, `lean_initialize`, `lean_io_result_mk_ok/error/is_ok`.
10. **C++ delegation** (`cmake/leanrt_cpp_partial/`) — Build a partial C++ static archive that excludes the modules Zig has taken over. Link `libleanrt-zig.a + libleanrt_cpp_partial.a` with no duplicate symbols.
11. **ABI smoke tests** (`tests/abi-smoke/*.c`) — C programs with `_Static_assert` and runtime checks. Run via `zig build test-abi`.
12. **Real Lean smoke test** (`tests/lean-smoke/`) — Compile a tiny `.lean` program with the baseline `lean` binary, link against Zig runtime, run, verify output.
13. **PoC report** (`docs/m2-poc-report.md`) — Symbol inventory, layout evidence, smoke results, performance snapshot, M3 recommendations.

M2 is sealed when the Lean smoke test binary runs to completion with correct output and no unresolved correctness gaps in the M2 subset.

## 4. Conventions for Adding Zig Implementations

### File layout
Mirror the upstream `src/runtime/` structure:

| Upstream C++ | Zig implementation |
|--------------|--------------------|
| `src/runtime/object.cpp` | `zig-backend/src/runtime/object.zig` |
| `src/runtime/apply.cpp` | `zig-backend/src/runtime/apply.zig` |
| `src/runtime/io.cpp` (subset) | `zig-backend/src/runtime/io_min.zig` |
| `src/include/lean/lean.h` | `zig-backend/include/lean/lean.h` (copy or symlink) |

### Function signatures
Every exported function must use `export` + `callconv(.c)`:

```zig
export fn lean_inc(o: lean_obj_arg) callconv(.c) void {
    // ...
}
```

### Struct definitions
Use `extern struct` for C ABI compatibility:

```zig
pub const lean_object = extern struct {
    m_rc: i32,
    m_cs_sz: u16,
    m_other: u8,
    m_tag: u8,
};
```

### Testing
1. Write Zig unit tests inside the `.zig` file using `test "description" { ... }`.
2. Write C ABI smoke tests in `tests/abi-smoke/*.c` with `_Static_assert` for layout and runtime checks for behavior.
3. Run `zig build test` and `zig build test-abi` before committing.

### Commit convention
One commit per feature inside `zig-backend/` using the lean4 style:

```
feat: M2-F1-object-model — bit-identical lean_object and tag constants
```

### Documentation
- Every deviation from C++ semantics (e.g., single-threaded allocator simplification) must be documented in `docs/m2-poc-report.md`.
- Every symbol still delegated to C++ must be listed in the PoC report.

## 5. Known Limitations (M1)

- `scan-commits.py` classifies commits based on file paths only. It does not analyze semantic impact (e.g., a commit touching both backend and frontend is classified backend-touching).
- `replay.py` produces best-effort `zig_target` mappings. Some historical path renames (e.g., `library/Init` → `src/Init`) may map imperfectly.
- The Zig build skeleton in M1 contains stub functions (`@panic("unimplemented")`). No runtime correctness is claimed until M2.
