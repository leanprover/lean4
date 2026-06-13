# zig-backend Contributor & Agent Guide

Rules and conventions for working in this repository (human or AI agent).
For project status and architecture, read [README.md](README.md) first.

## Write boundary

- Write only inside `zig-backend/`. The outer lean4 repository is a build
  dependency, not a workspace — never modify it (the only historical
  exception is the one-line `zig-backend/` entry in its `.gitignore`).
- Never delete or manually edit `<lean4>/build/`, `<lean4>/stage0/`, or any
  other outer-repo artifact. `stage0/` is a generated snapshot of `src/`.

## ABI preservation — the contract

`<lean4>/src/include/lean/lean.h` is the C ABI between Lean-emitted code and
the runtime. The Zig runtime MUST:

1. Provide **bit-identical struct layouts** for every type declared in
   `lean.h`. Enforced by comptime asserts in `src/runtime/object.zig` and
   `_Static_assert`s in `tests/abi-smoke/layout.c`.
2. **Export every required `LEAN_EXPORT` symbol** with matching name,
   calling convention (`callconv(.c)`), and observable semantics. Verified
   by `tools/check-symbols.sh` (must print `Missing symbols: 0`).
3. Honor the ownership conventions: `lean_obj_arg` (callee consumes RC),
   `b_lean_obj_arg` (caller retains RC), `u_lean_obj_arg` (exclusive).

If an implementation cannot satisfy the ABI, that is a blocker — stop and
surface it. Do NOT modify `lean.h`.

## Paths and environment

Nothing in this repository may hardcode an absolute path. Every consumer
resolves paths in this order: build option / CLI flag → environment
variable → relative default.

| Env var | Meaning | Default |
| --- | --- | --- |
| `LEAN4_DIR` | lean4 repository root | parent of `zig-backend/` |
| `GMP_PREFIX` | GMP installation prefix | `/opt/homebrew/opt/gmp` |
| `LIBUV_PREFIX` | libuv installation prefix | `/opt/homebrew/opt/libuv` |

## Build and test commands

```bash
zig build                  # split runtime archives
zig build test             # unit tests (works without a stage1 build)
zig build test-abi         # C ABI smoke tests
zig build test-all         # every suite (excludes scheduler-diff, see ROADMAP)
./tools/check-symbols.sh   # symbol surface check
(cd src/EmitZig && lake build && lake test)   # EmitZig package (stage1 lake)
python3 -m pytest tools/tests -q              # tooling tests
```

Use the stage1 `lake`/`lean` from `$LEAN4_DIR/build/release/stage1/bin` for
the EmitZig package. A clean rebuild gate before sealing significant work:

```bash
rm -rf zig-out .zig-cache && zig build test-all && ./tools/check-symbols.sh
```

## Success criteria

Never report success unless the relevant verification commands above pass.
For runtime changes that touch exported symbols, `check-symbols.sh` must
still print `Missing symbols: 0`.

## Test-driven development (mandatory)

1. **Red**: write failing tests first (Zig `test` blocks in the module,
   plus a C ABI smoke test in `tests/abi-smoke/` when the change touches
   exported surface).
2. **Green**: implement just enough to pass.
3. Iterate.

## Code conventions

- Exported runtime functions: `export fn lean_*(…) callconv(.c)`; ABI
  structs are `extern struct`.
- Module layout mirrors upstream `src/runtime/*.cpp` names where a
  counterpart exists (e.g. `object.zig`, `apply.zig`, `string.zig`).
- `src/runtime/root.zig` re-exports every module and force-references it in
  a `comptime` block — new modules must be added there and to the
  `runtime_modules` list in `build.zig`.
- `src/runtime/task_tls.zig` is a deliberate boundary module shared by
  `task.zig` and `task_manager.zig` (documented in
  `docs/m5b-tls-boundary.md`); do not inline it into either side.
- Every deviation from C++ semantics must be documented (module doc comment
  and, for milestone work, the relevant report in `docs/`).

## Commit convention

One commit per logical change, lean4 style:

```
<type>: <imperative, lowercase subject>
```

with `type` ∈ `feat`, `fix`, `test`, `refactor`, `doc`/`docs`, `chore`,
`build`, `ci`, `perf`. Keep the body focused on why.

## When to stop and surface a blocker

- The work would require modifying files outside `zig-backend/`.
- The ABI cannot be satisfied (layout or semantics).
- The lean4 stage1 baseline is missing or broken.
- A required tool or dependency is missing.
