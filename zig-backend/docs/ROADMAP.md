# Roadmap: M7 → M9

Status after M6: the runtime and the EmitZig backend are sealed for the
smoke-program surface. This document lists what stands between that state
and a backend that can compile real stdlib workloads (M7), a runtime with
no panic stubs on reachable paths (M8), and upstream promotion (M9).

## M7 — Widen EmitZig from smoke programs to stdlib slices

The backend currently panics outside the tested cone. All locations are in
`src/EmitZig/EmitZig.lean`:

| Line | Gap | Notes |
| --- | --- | --- |
| 431 | missing EmitZig signature in `fap` | should not occur in well-formed LCNF; needs a real error |
| 451 | failed extern application fallback | mirror EmitC's extern classification |
| 458 | missing EmitZig signature in `pap` | as 431 |
| 682 | unsupported `LetValue` fallback | catch-all; eliminate by construction |
| 689 | multi-`inc` (RC multiplicity > 1) | normalize or emit `lean_inc_n` |
| 699 | multi-`dec` | as above |
| 747 | pure `cases` fallback | unreachable for the impure subset; replace with a proper error |
| 890 | "body emission not implemented" | generic escape hatch |

Work items, roughly in dependency order:

1. **Closed-term / ground-value emission** — no `emitGroundDecl` equivalent
   exists. This is the main blocker for compiling stdlib-heavy modules.
   Decide whether to mirror EmitC's constant-pool layout exactly or
   construct at module init.
2. **Eliminate the panic placeholders** above so EmitZig is total over the
   same LCNF body space as EmitC.
3. **Systematic `InlineHelpers.lean` expansion** — 24 of ~564 `static
   inline` helpers from `lean.h` are translated; the rest fall back to
   extern calls into the runtime where exported. Expand driven by what
   stdlib slices actually reach, not by hand-picking. The hand-table
   approach itself is sustainable (hot path is covered; extern fallback
   bridges the rest).
4. **Opaque `@[extern]` coverage** aligned with EmitC's classification.
5. **Larger differential fixtures** — compile growing stdlib slices through
   both backends and diff; add each as a reproducible `emitzig-diff` case.
6. **`varMangleCache`** — upstream EmitC caches mangled names; EmitZig
   re-mangles per call. Add when profiling shows it matters.

## M8 — Runtime gap closure

1. **Allocator ownership across mixed links** (highest priority — currently
   breaks a test): commit `bc77bd52` switched `alloc.zig`'s
   `freeLegacySmall` from the size-prefix `free(ptr - 8)` layout to
   `mi_free(ptr)` (matching the mimalloc-built baseline runtime), but in
   binaries that link the full upstream `libleanrt` (real mimalloc) next to
   the Zig runtime — the `scheduler-smoke` configuration — `mi_free`
   segfaults in `mi_free_generic_mt` on pointers it does not own (objects
   the Zig allocator handed out). `zig build scheduler-diff` is broken and
   excluded from `test-all` until the legacy-free path can prove ownership.
   Harnesses that link without mimalloc provide weak `malloc`-backed stubs
   (`src/runtime/testabi_hidden_shims.c`, `tests/abi-smoke/bignum.c`,
   `tests/bignum-smoke/*.c`). Note the same commit also invalidated the
   old prefix-layout legacy fixtures in `tests/abi-smoke/st_ref.c` and
   `float.c`; those now fabricate mimalloc-layout objects.
2. **Unconditional pre-payload read in `hasTrackedMeta`** — classifying a
   pointer reads `@sizeOf(AllocationMeta)` bytes before it; for objects not
   allocated by the Zig tracker this is an out-of-bounds read that can
   fault at page boundaries (observed as a Bus error in the alloc unit
   tests before the test helper was made page-safe). A real ownership test
   is needed instead of the magic-value probe.
3. **Unimplemented stubs** that panic at runtime if reached:
   `string.zig` (`lean_string_mk`, `lean_string_data`,
   `lean_string_utf8_set`, `lean_string_utf8_extract`), `debug.zig`
   (`lean_dbg_trace`, `lean_dbg_sleep`, `lean_dbg_trace_if_shared`),
   `io_min.zig` (`lean_decode_io_error`, `lean_decode_uv_error`).
4. **`io_error.zig` deduplication** — ~500 LOC of repetitive constructors;
   replace with a table/factory while keeping the exported surface
   bit-identical.
5. **ABI regression harness** — a C suite that exercises every exported
   function family at runtime (beyond layout asserts), run in `test-all`.
6. **TLS lifecycle documentation/enforcement** — `initializeThreadAllocator`
   / `finalizeThreadAllocator` contracts are implicit; a thread exiting
   without finalization leaks its free lists.
7. **MPZ compactor payload divergence** — Zig `LeanMPZ` payload is 48 bytes
   vs 32 upstream; only header-prefix compatible. Affects compact regions.

## M9 — Upstream promotion

1. Move `EmitZig.lean` into `src/Lean/Compiler/LCNF/EmitZig.lean`, wire it
   into the compiler pipeline, audit stage0/build-system fallout.
2. Replace `leanc`-driven C compilation with a `zig cc` toolchain path.
3. Decide the runtime story upstream: ship the split archives or complete
   the C++ delegation surface first.

## Deferred-risk register

Reviewed and deliberately **not** done; revisit with dedicated verification:

- **panic → error conversions** in the runtime (e.g. `apply.zig` null
  closure, promise deactivation in `rc.zig`): the ABI has no error channel
  for these paths; changing observable behavior risks divergence from C++.
- **Atomic ordering relaxation** (`.seq_cst` → `.acq_rel`/`.acquire` in
  `rc.zig`, `task.zig`): performance-only; needs a memory-model review and
  TSan runs (TSan was unavailable on the original host, see
  `library/m5-readiness.md`).
- **Inlining `task_tls.zig`**: rejected — it is imported by both `task.zig`
  and `task_manager.zig`; merging it into either side inverts the layering
  (documented boundary, `docs/m5b-tls-boundary.md`).
- **Splitting `EmitZig.lean` into submodules**: upstream EmitC is a single
  file; staying monolithic keeps the M9 diff reviewable.
