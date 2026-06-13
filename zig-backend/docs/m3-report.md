# M3 report

This report closes milestone **M3** for the Lean 4 Zig runtime mission. It
records the final symbol inventory, allocator-reclaim outcome, regression
status versus the sealed M2 contract, and the last-minute cleanup work required
to make the full M3 validation sequence pass from a clean build.

## Executive summary

- Zig-owned public `lean.h` symbols increased from **68** at M2 close to
  **133** at M3 close (**+65**).
- `./tools/check-symbols.sh` now reports **Missing symbols: 0** with
  **209 runtime-required header symbols** and **0 exclusions**.
- The M2 contract remains intact: `validation-state.json` still shows all
  **80** M1/M2/cross assertions as `passed`.
- The allocator reclaim did **not** reintroduce the historical
  `initialize_Init_Data_Random` crash. Both smoke commands still print
  `Hello, world!`.
- `tests/lean-smoke/leaks-suppressions.txt` was **retained** rather than
  emptied. M3 therefore finishes in **Option B kept** state, not Option A.

## Final inventory snapshot

### Public-surface totals

| Status | M2 | M3 | Delta |
| --- | ---: | ---: | ---: |
| Zig-owned | 68 | 133 | +65 |
| C++-delegated | 112 | 76 | -36 |
| not-yet | 29 | 0 | -29 |
| multiply-defined | 0 | 0 | 0 |

The totals still reconcile to the full public `lean.h` surface of **209**
`LEAN_EXPORT` declarations.

### Family-by-family delta from M2

| Family | Count | M2 owner | M3 owner | Notes |
| --- | ---: | --- | --- | --- |
| allocator reclaim | 9 | 6 delegated + 3 not-yet | Zig | `lean_alloc_object`, `lean_free_object`, heartbeat, size helpers, external-class registration, and the 3 small-allocation exports now live in `libleanrt-zig.a` |
| IO error constructors + `lean_mk_io_user_error` | 25 | not-yet | Zig | Exported from Zig with weak C wrappers so stage1 `libInit.a` can still override at smoke-link time |
| `lean_st_ref_reset` | 1 | not-yet | Zig | Implemented in the same Zig ref-cell module used by the rest of the `st_ref` family |
| float helpers | 14 | delegated | Zig | `frexp`, `isfinite`, `isinf`, `isnan`, `scaleb`, `to_string`, and float/float32 `once_cold` mirrors |
| once-cold helpers | 6 | delegated | Zig | `lean_obj_once_cold` plus the uint/usize variants |
| dbg helpers | 3 | delegated | Zig | `lean_dbg_trace`, `lean_dbg_trace_if_shared`, `lean_dbg_sleep` |
| `st_ref` helpers | 4 | delegated | Zig | `lean_st_mk_ref`, `lean_st_ref_get`, `lean_st_ref_set`, `lean_st_ref_swap` |
| misc helpers | 3 | delegated | Zig | `lean_name_eq`, `lean_slice_hash`, `lean_slice_dec_lt` |

The table sums to **65** symbols, which exactly explains the M2→M3 Zig-owned
increase from 68 to 133.

### Archive / footprint snapshot

Measured after the final clean rebuild:

| Artifact | Value |
| --- | --- |
| `zig-out/lib/libleanrt-zig.a` | `3,526,456` bytes |
| `zig-out/lib/libleanrt_cpp_partial.a` | `548,088` bytes |
| `zig-backend/` footprint | `191M` |
| Zig-owned public symbol count | `133` |

## Allocator reclaim outcome (M3-C)

The allocator reclaim is green.

### What changed

The default build now exports the allocator-owned public ABI from
`libleanrt-zig.a`, not from `libleanrt_cpp_partial.a`. The reclaimed set is:

- `lean_alloc_object`
- `lean_free_object`
- `lean_inc_heartbeat`
- `lean_object_byte_size`
- `lean_object_data_byte_size`
- `lean_register_external_class`
- `lean_alloc_small`
- `lean_free_small`
- `lean_small_mem_size`

The symbol audit confirms that all nine are Zig-owned and absent from the
delegated C++ archive.

### Did the M2-F11b crash recur?

No.

The clean-smoke validation still succeeds after the reclaim:

- `bash tests/lean-smoke/run.sh` exits `0`
- the program still prints `Hello, world!`
- `zig build test` and `zig build test-abi` stay green
- `./tools/check-symbols.sh` reports `Missing symbols: 0`

This means the earlier mixed-allocator crash around
`initialize_Init_Data_Random` did not come back in the final M3 build.

### Did dropping the mpz suppression succeed?

No. The mission does **not** finish in “suppression removed” state.

During the final sweep, an empty suppression file exposed a failing leak audit.
That failure was **not** the old allocator crash; instead it uncovered a
separate runtime bug in the Zig `lean_obj_once_cold` implementation: heap
objects cached through `once_cold` were not being marked persistent, so the
Lean smoke program reported a real unsuppressed root leak through
`lean_obj_once_cold` during `Init.Data.Repr` initialization.

The cleanup fix was to mirror upstream behavior and call the equivalent of
`lean_mark_persistent` for object-valued `once_cold` results. After that fix,
`LEAN_SMOKE_CHECK_LEAKS=1 bash tests/lean-smoke/run.sh` returns `0` again.

However, `tests/lean-smoke/leaks-suppressions.txt` was **retained** with the
historical delegated-frame entry:

```text
lean::mpz::mpz(lean::mpz const&)
```

So the final recorded state for M3 is:

- **Option A (suppression removed): not achieved**
- **Option B (suppression retained): achieved**

## Per-area implementation notes

### M3-C — allocator reclaim

- The archive boundary is now the intended one for M4/M5 follow-up work:
  allocator exports are back in Zig by default.
- The split-runtime model remains intact: no duplicate public definitions were
  introduced and the combined archive surface still matches `lean.h`.
- The clean sweep also proved that leak-check stability depends on correct
  persistent handling for `lean_obj_once_cold`; this was surfaced only during
  final validation, not by the original allocator-reclaim smoke.

### M3-A — not-yet surface closed out

- All public IO error constructors declared in `lean.h` are now covered by the
  split runtime.
- The `lean_mk_io_error_*` family needed weak-link layering because stage1
  `libInit.a` already contributes the same names at smoke-link time. The final
  arrangement keeps the ABI surface available to direct runtime consumers while
  allowing the Lean stdlib definitions to coexist during stage1 linking.
- `lean_st_ref_reset` is now provided by Zig and validated through ABI smoke.

### M3-B — delegated helper families moved into Zig

- Float helpers, once-cold helpers, dbg helpers, `st_ref` helpers, and
  name/slice helpers all moved from delegated C++ ownership to Zig ownership.
- The final cleanup found one semantic mismatch inside the new once-cold path:
  object-valued caching must mark results persistent, not merely cached. This
  was fixed in `src/runtime/once_cold.zig`, and new unit / ABI checks cover the
  heap-object case.
- The `st_ref` ABI smoke also needed a small expectation correction: after
  `lean_st_ref_get`/`lean_dec`, the original value is still shared between the
  local retained handle and the ref cell until `set`/`swap` releases it.

## Regression status against M2

M2 remains sealed:

- `validation-state.json` still reports **80 / 80** M1+M2+cross assertions as
  `passed`
- no M2 assertion regressed during the M3 sweep
- the outer Lean repo remains clean outside the already-allowed `.gitignore`
  change and the mission-owned `zig-backend/` directory

The most visible M2-era improvements preserved by M3 are:

- `zig build` clean-rebuild reproducibility
- green Zig unit tests
- green ABI smoke tests
- green Lean end-to-end smoke (`Hello, world!`)
- green combined symbol audit

## Final verification transcript

The final green validation set is:

```bash
cd /Users/davirian/dev/active/lean4/zig-backend
rm -rf zig-out .zig-cache
zig build
zig build test
zig build test-abi
bash tests/lean-smoke/run.sh
LEAN_SMOKE_CHECK_LEAKS=1 bash tests/lean-smoke/run.sh
./tools/check-symbols.sh
```

Observed outcomes:

- clean rebuild succeeds from empty `zig-out/` and `.zig-cache/`
- `zig build test` passes after adding the object-persistence coverage for
  `lean_obj_once_cold`
- `zig build test-abi` passes with the strengthened `once_cold` smoke and the
  corrected `st_ref` expectation
- plain smoke still prints `Hello, world!`
- leak smoke exits `0` after the `once_cold` persistence fix
- `./tools/check-symbols.sh` reports `Missing symbols: 0`
- the public Zig-owned symbol count is **133**, comfortably above the mission
  floor of **120**

## Deferred follow-ups

### M4 — bignums / GMP

- The remaining delegated surface is still dominated by bignum / conversion
  families (`lean_nat_big_*`, `lean_int_big_*`, `lean_big_*`,
  `lean_*_of_big_*`).
- M4 should revisit the retained suppression file after the GMP path is ported
  or otherwise removed from the delegated runtime. That is the earliest point
  where “Option A success” can be claimed with confidence.

### M5 — IO, tasks, libuv

- Task manager, cancellation, `lean_run_main`, `lean_io_*_core`, `lean_task_*`,
  and the libuv/process surface remain delegated.
- M5 should treat the allocator and `once_cold` fixes from M3 as prerequisites:
  more of the real initialization and async runtime will stress both paths.

### M6 — EmitZig

- M6 can assume a much larger Zig-owned runtime foundation now that 133 public
  ABI symbols are native.
- The weak-link IO error arrangement should be treated as a layering contract:
  EmitZig must preserve the same external ABI while deciding whether these
  constructors remain runtime-provided, stdlib-provided, or both.

## Bottom line

M3 closes with the intended runtime-surface expansion complete, the allocator
reclaim validated, the M2 contract still intact, and the final cleanup issues
resolved. The milestone exits with **133 Zig-owned public symbols**, **0**
missing required symbols, a green clean rebuild, and **Option B retained** for
the historical leak-suppression file.
