# Lean 4 Zig Backend

A Zig reimplementation of the Lean 4 compiler backend, developed as a shadow
tree inside a lean4 checkout. Two pillars:

1. **Runtime** (`src/runtime/`, ~12.4k LOC Zig): a drop-in, ABI-compatible
   replacement for the C++ runtime in `<lean4>/src/runtime/`. Lean-emitted C
   code links against it unchanged.
2. **Code generator** (`src/EmitZig/`, ~1.4k LOC Lean): `EmitZig`, an LCNF
   backend that emits Zig instead of C, mirroring the structure of upstream
   `src/Lean/Compiler/LCNF/EmitC.lean`.

The outer lean4 repository is never modified; everything lives under
`zig-backend/`, which is its own git repository.

## Milestone status

| Milestone | Scope | Status |
| --- | --- | --- |
| M1 | Foundations: commit scan/replay tooling, build skeleton | sealed |
| M2 | ABI-compatible runtime PoC: object model, RC, allocator, closures, strings, arrays, split-runtime link, end-to-end Lean smoke test | sealed |
| M3 | Allocator reclaim (`lean_alloc_object` family owned by Zig) and delegated-family cleanup | sealed |
| M4 / M4b | Bignum: `mpz_zig` GMP bindings, Nat/Int arithmetic, GMP differential oracle | sealed |
| M5 / M5b | Tasks: task manager, promises, cancellation, TLS boundary, scheduler differential | sealed |
| M6 | EmitZig shadow-tree backend, byte-identical stdout vs EmitC on the smoke programs | sealed |
| M7+ | Widen EmitZig coverage, close runtime gaps, upstream promotion | see [docs/ROADMAP.md](docs/ROADMAP.md) |

See [docs/INDEX.md](docs/INDEX.md) for the milestone reports in reading order.

## Architecture

### Split runtime

`zig build` produces two static archives that together replace the upstream
monolithic `libleanrt.a`:

- `zig-out/lib/libleanrt-zig.a` — the Zig-owned runtime (object model,
  reference counting, allocator, closures, strings, arrays, Nat/Int bignums,
  tasks/promises, IO results and errors).
- `zig-out/lib/libleanrt_cpp_partial.a` — the still-delegated upstream C++
  remainder (compacted regions, libuv event loop, stack overflow handling,
  …), built by CMake from `<lean4>/src/runtime/` with the Zig-owned symbols
  hidden (`cmake/leanrt_cpp_partial/`).

`tools/check-symbols.sh` verifies the union of both archives covers every
runtime-required `LEAN_EXPORT` symbol in `lean.h`.

### ABI contract

`<lean4>/src/include/lean/lean.h` is the contract and is never modified.
Struct layouts are bit-identical (enforced by comptime asserts in
`src/runtime/object.zig` and `_Static_assert`s in `tests/abi-smoke/`), every
exported function uses `callconv(.c)`, and the `lean_obj_arg` /
`b_lean_obj_arg` ownership conventions match the C++ runtime. See
[AGENTS.md](AGENTS.md) for the full rules.

### EmitZig

`src/EmitZig/` is a standalone Lake package. `lake exe emitzig in.lean -o
out.zig` elaborates a module with the stage1 toolchain and emits Zig from its
LCNF. `InlineHelpers.lean` carries hand-translated Zig bodies for the
`static inline` helpers of `lean.h` that EmitC gets for free from the C
preprocessor. The differential harness (`zig build emitzig-diff`) checks the
EmitZig path produces byte-identical stdout to the EmitC path.

## Prerequisites

- Zig 0.16.0
- A built lean4 stage1 tree at `<lean4>/build/release/stage1`
  (`make -j$(nproc) -C build/release` in the outer repo)
- CMake, a C/C++ toolchain, GMP and libuv (homebrew prefixes by default)
- Python 3 for the tooling

All paths are configurable; each value resolves as build option → environment
variable → default:

| Build option | Env var | Default |
| --- | --- | --- |
| `-Dlean4-dir=…` | `LEAN4_DIR` | parent directory of `zig-backend/` |
| `-Dgmp-prefix=…` | `GMP_PREFIX` | `/opt/homebrew/opt/gmp` |
| `-Dlibuv-prefix=…` | `LIBUV_PREFIX` | `/opt/homebrew/opt/libuv` |

## Quick start

```bash
cd zig-backend
zig build              # split runtime archives into zig-out/lib/
zig build test         # Zig unit tests (no stage1 needed)
zig build test-all     # every suite: unit, abi, link, smoke, differential
./tools/check-symbols.sh
```

## Test taxonomy

| Step | What it covers |
| --- | --- |
| `zig build test` | Zig unit tests per runtime module (+ GMP oracle for `mpz_zig`) |
| `zig build test-abi` | C programs asserting layouts, RC semantics, allocator behavior, tasks |
| `zig build link-check` | Links a mixed Zig/C++ consumer to catch duplicate symbols |
| `zig build emitzig-smoke` | Compiles and runs the EmitZig smoke programs |
| `zig build emitzig-diff` | EmitZig vs EmitC stdout differential |
| `zig build task-smoke` | M5 task/promise EmitZig programs + differential |
| `zig build bignum-diff` | Randomized Nat/Int differential vs a GMP reference |
| `zig build lean-smoke` | End-to-end: stage1 `lean -c` → cc → split runtime → run |
| `zig build scheduler-diff` | Scheduler differential vs frozen C++ reference (**currently broken**, see roadmap) |
| `zig build test-all` | All of the above except `scheduler-diff` |
| `(cd src/EmitZig && lake test)` | EmitZig emission unit/regression tests |

CI (`.github/workflows/ci.yml`) runs the pure-Zig `zig build test` subset;
everything that needs the stage1 tree is a local gate.

## Directory map

```
zig-backend/
├── build.zig            # Zig build: runtime archives, all test steps
├── cmake/               # leanrt_cpp_partial: delegated C++ archive build
├── include/             # lean.h mirrored via relative symlinks
├── src/
│   ├── runtime/         # the Zig runtime (root.zig re-exports all modules)
│   ├── mpz_zig.zig      # GMP bindings used by the bignum modules
│   └── EmitZig/         # Lake package: the EmitZig LCNF backend + tests
├── tests/
│   ├── abi-smoke/       # C ABI assertions (zig build test-abi)
│   ├── bignum-smoke/    # GMP differential harness
│   ├── emitzig-smoke/   # EmitZig smoke + differential programs
│   ├── lean-smoke/      # end-to-end Lean → C → split-runtime test
│   └── scheduler-smoke/ # scheduler differential vs frozen reference
├── tools/               # commit scanner, replay, symbol checker (+ tests)
├── sync/                # per-commit scan reports (M1 tooling output)
├── replays/             # markdown replay summaries
├── docs/                # milestone reports, ROADMAP, INDEX
└── library/             # m5 readiness notes
```

## Documentation

- [AGENTS.md](AGENTS.md) — contributor/agent guide: rules, commands, conventions
- [docs/INDEX.md](docs/INDEX.md) — all documents in reading order
- [docs/ROADMAP.md](docs/ROADMAP.md) — M7–M9 plan and known gaps
- [docs/STATUS-zh.md](docs/STATUS-zh.md) — 中文项目总览
