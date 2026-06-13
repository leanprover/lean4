# M4 report

This report closes the M4 bignum milestone for the split Lean 4 Zig runtime in
`zig-backend/`. It records the actual Zig LOC footprint, the Layer A/B/C
coverage matrix, the differential evidence for the new bignum surface, the
cross-archive compactor status, the no-regression check against already-sealed
milestones, and the clean-state reproducibility sweep.

## Scope and acceptance snapshot

M4's close-out bar was:

1. keep the bignum Zig footprint within budget,
2. prove Layer A/B/C coverage and preserve the M4a/M4b validation results,
3. show differential evidence for both the ABI surface and the EmitZig coupling,
4. document the cross-archive compactor limitation without regressing the
   existing `compact.cpp` consumer,
5. keep all sealed M1/M2/M3/M6/P1 assertions green,
6. keep the outer Lean repo clean outside the already-allowed exclusions,
7. rerun the clean-state sequence
   `lake build && zig build && zig build emitzig-smoke && bash tests/emitzig-smoke/bignum/run.sh && zig build emitzig-diff`
   after moving `.lake`, `zig-out`, and `.zig-cache` out of the way.

Current snapshot:

- **M4a:** `45 / 45` assertions passed in `validation-state.json`.
- **M4b:** `42 / 42` assertions passed in `validation-state.json`.
- **M4c implementation evidence:** green locally; the milestone's validation
  rows remain `pending` only because the dedicated M4c validator has not yet
  rewritten `validation-state.json`.
- **No regression:** M1, M2, M3, M6, and P1 remain fully passed.
- **Outer repo boundary:** clean outside `.gitignore` and `zig-backend/`.
- **Reproducibility sweep:** exit `0` end-to-end from a moved-away-cache state.

## No-regression summary

The report requirement for M4c is specifically that already sealed milestones
remain green. The current `validation-state.json` still reports:

| Milestone | Passed / total assertions | Status |
| --- | ---: | --- |
| `M1` | `26 / 26` | passed |
| `M2` | `49 / 49` | passed |
| `M3` | `30 / 30` | passed |
| `M6` | `44 / 44` | passed |
| `P1` | `9 / 9` | passed |

That means the bignum work did **not** break:

- the workspace/bootstrap/tooling baseline from M1,
- the split runtime ABI + lean-smoke path from M2,
- the allocator reclaim / delegated-family cleanup from M3,
- the shadow-tree EmitZig MVP from M6,
- the P1 repo-hygiene and reproducibility fixes.

## Zig LOC budget

### Measurement method

The budget table below counts **non-blank, non-comment Zig LOC** for the
mission-owned M4 bignum implementation files. This keeps the count focused on
the shipped runtime/codegen surface rather than blank lines, comments, or the
surrounding C/Lean test harness.

### Per-file LOC table

| File | Non-comment Zig LOC |
| --- | ---: |
| `src/mpz_zig.zig` | 867 |
| `src/runtime/mpz_object.zig` | 73 |
| `src/runtime/nat_constructors.zig` | 109 |
| `src/runtime/nat_arith_part1.zig` | 170 |
| `src/runtime/nat_arith_part2.zig` | 196 |
| `src/runtime/nat_compare_bitwise.zig` | 158 |
| `src/runtime/nat_shift_pow_gcd_log2.zig` | 203 |
| `src/runtime/int.zig` | 580 |
| `src/runtime/int_conv.zig` | 78 |
| **Total** | **2434** |

The total is **2434 LOC**, so it remains within the required `<= 2500` cap.

### Why the total is near the ceiling

The total lands in the `2200-2500` band for two predictable reasons:

1. `src/mpz_zig.zig` deliberately co-locates the full GMP differential surface
   instead of scattering that compatibility logic across many helpers. That kept
   the 45/45 readiness mapping easy to audit while M4 was still stabilizing.
2. `src/runtime/int.zig` keeps the Int constructor, arithmetic, div-family, and
   compare ownership/RC edge cases in one place. Splitting that file further
   during M4 would have reduced local readability more than it would have helped
   milestone risk.

For context only, the shared integration touch-ups outside the dedicated M4
modules were small: `build.zig` added 136 Zig lines, and the pre-existing shared
runtime files (`alloc.zig`, `lean_object.zig`, `object.zig`, `root.zig`,
`uint.zig`) added a further 208 lines of M4-specific glue. The main budgeted
runtime surface is still the 2434-LOC table above.

## Layer A / B / C coverage matrix

Status vocabulary used here:

- **passed** = shipped and validated by the current M4a/M4b/M4c evidence,
- **deferred** = intentionally not completed in M4, but documented and tracked,
- **skipped** = not applicable for the current milestone closeout.

No rows are currently skipped. The only still-deferred item is the
payload-equivalent compactor round-trip for the Zig `Mpz` layout.

### Coverage matrix

| Layer | Symbols / surface | Status | Evidence / note |
| --- | --- | --- | --- |
| A | `mpz_init`, `mpz_init_set`, `mpz_init_set_str`, `mpz_init_set_ui`, `mpz_init_set_si`, `mpz_set`, `mpz_set_str`, `mpz_set_ui`, `mpz_set_si`, `mpz_swap`, `mpz_clear` | passed | All mapped in `src/mpz_zig.zig`; `zig build test` covers init/set/swap/teardown through the `Mpz.* matches GMP` suite. |
| A | `mpz_sgn`, `mpz_fits_sint_p`, `mpz_fits_uint_p`, `mpz_size`, `mpz_get_si`, `mpz_get_ui`, `mpz_getlimbn` | passed | Covered by the `fits*`, `get*`, `getLimb`, and sign/size tests in `src/mpz_zig.zig`; readiness note: `mpz_size` still uses wrapper metadata rather than a dedicated std API. |
| A | `mpz_cmp`, `mpz_cmp_ui`, `mpz_cmp_si` | passed | `Mpz.cmp`, `Mpz.cmpUint`, and `Mpz.cmpInt` differential tests are green. |
| A | `mpz_add`, `mpz_add_ui`, `mpz_sub`, `mpz_sub_ui`, `mpz_mul`, `mpz_mul_ui`, `mpz_mul_si`, `mpz_neg` | passed | Arithmetic differential tests are green; the scalar variants still use wrapper shims rather than a single std call, but the M4 readiness outcome is still `passed`. |
| A | `mpz_divexact`, `mpz_tdiv_qr`, `mpz_tdiv_r`, `mpz_tdiv_q`, `mpz_tdiv_q_ui` | passed | `Mpz.divExact`, `Mpz.divTruncQR`, quotient, and remainder behavior match GMP; the scalar-divisor fast path remains a wrapper shim, not a blocker. |
| A | `mpz_pow_ui`, `mpz_sizeinbase` | passed | `Mpz.pow`, `Mpz.log2`, `Mpz.bitCountAbs`, and string-size behavior are tested; readiness note: `pow` still inherits the `u32` exponent cap and `sizeinbase` is derived rather than direct. |
| A | `mpz_and`, `mpz_ior`, `mpz_xor` | passed | `Mpz.bitAnd`, `Mpz.bitOr`, and `Mpz.bitXor` differential tests are green. |
| A | `mpz_mul_2exp`, `mpz_tdiv_q_2exp`, `mpz_fdiv_r_2exp`, `mpz_fdiv_q_2exp` | passed | `Mpz.mul2k`, `Mpz.div2k`, `Mpz.modPow2`, and `Mpz.smodPow2` are green; floor-vs-trunc behavior is handled by explicit wrapper logic. |
| A | `mpz_gcd`, `mpz_get_str` | passed | `Mpz.gcd`, `Mpz.toString`, and `Mpz.setStr` tests all pass. |
| A | payload-equivalent compactor round-trip against the Zig `Mpz` object layout | deferred | Header-prefix compatibility is proven; full payload equivalence is blocked by `sizeof(MpzObject)==48` vs `sizeof(mpz_object)==32` and requires a rewritten `insert_mpz`/deserializer pair. |
| B | `lean_nat_big_succ`, `lean_nat_big_add`, `lean_nat_big_sub`, `lean_nat_big_mul` | passed | `M4a-D` is `6 / 6` green; covered by `nat_arith_part1.zig`, ABI smoke, and differential Nat checks. |
| B | `lean_nat_big_div`, `lean_nat_big_div_exact`, `lean_nat_big_mod` | passed | `M4a-E` is `6 / 6` green; zero-divisor RC behavior matches upstream object.cpp. |
| B | `lean_nat_big_eq`, `lean_nat_big_le`, `lean_nat_big_lt`, `lean_nat_big_land`, `lean_nat_big_lor`, `lean_nat_big_xor` | passed | `M4a-F` is `6 / 6` green; compare and bitwise identities are covered in both unit and ABI smoke paths. |
| B | `lean_nat_shiftl`, `lean_nat_big_shiftr`, `lean_nat_pow`, `lean_nat_gcd`, `lean_nat_log2` | passed | `M4a-G` is `7 / 7` green; panic behavior and RC discipline are covered. |
| B | `lean_int_big_neg`, `lean_int_big_add`, `lean_int_big_sub`, `lean_int_big_mul` | passed | `M4b-B` is `5 / 5` green; algebraic invariants and allocator balance hold. |
| B | `lean_int_big_div`, `lean_int_big_div_exact`, `lean_int_big_mod`, `lean_int_big_ediv`, `lean_int_big_emod` | passed | `M4b-C` is `6 / 6` green; zero-divisor pointer/RC behavior matches upstream. |
| B | `lean_int_big_eq`, `lean_int_big_le`, `lean_int_big_lt`, `lean_int_big_nonneg` | passed | `M4b-D` is `5 / 5` green; compare semantics match GMP. |
| C | `lean_alloc_mpz`, `lean_extract_mpz_value` | passed | `M4a-B` is `6 / 6` green; `zig build test-abi` prints the expected LeanMPZ compactor INFO line and exits `0`. |
| C | `lean_cstr_to_nat`, `lean_big_usize_to_nat`, `lean_big_uint64_to_nat`, `lean_nat_overflow_mul` | passed | `M4a-C` is `6 / 6` green; scalar/big boundary and panic behavior are covered. |
| C | `lean_cstr_to_int`, `lean_big_int_to_int`, `lean_big_size_t_to_int`, `lean_big_int64_to_int`, `lean_big_int_to_nat` | passed | `M4b-A` is `4 / 4` green; consume-arg behavior for `lean_big_int_to_nat` is covered. |
| C | `lean_uint8_of_big_nat`, `lean_uint16_of_big_nat`, `lean_uint32_of_big_nat`, `lean_uint64_of_big_nat`, `lean_int8_of_big_int`, `lean_int16_of_big_int`, `lean_int32_of_big_int`, `lean_int64_of_big_int`, `lean_usize_of_big_nat`, `lean_isize_of_big_int`, `lean_uint64_mix_hash` | passed | `M4b-E` is `6 / 6` green; the width-conversion ABI and differential harnesses both pass. |

### Readout

- **Layer A** shipped with the full 45/45 readiness set accounted for.
- **Layer B** shipped all Nat/Int big arithmetic, compare, and shift/pow/gcd
  exports required by M4a/M4b.
- **Layer C** shipped the LeanMPZ bridge, constructors, and width conversions.
- The only remaining **deferred** item is not a public symbol gap; it is the
  deeper cross-archive compactor payload-compatibility problem described below.

## Differential and unit-test evidence

### Layer A unit comparison (`zig build test`)

`zig build test` exits `0` against the M4-owned Zig runtime modules. The most
important Layer A differential cases are embedded directly in
`src/mpz_zig.zig`:

- `Mpz.add matches GMP`
- `Mpz.sub matches GMP`
- `Mpz.mul matches GMP`
- `Mpz.divTruncQR matches GMP`
- `Mpz.divFloor matches GMP`
- `Mpz.ediv matches GMP`
- `Mpz.emod matches GMP`
- `Mpz.divExact matches GMP`
- `Mpz.neg matches GMP`
- `Mpz.pow matches GMP`
- `Mpz.gcd matches GMP`
- `Mpz.bitAnd / bitOr / bitXor matches GMP`
- `Mpz.mul2k / div2k / modPow2 / smodPow2 matches GMP`
- `Mpz.cmp / cmpInt / cmpUint matches GMP`
- `Mpz.fitsInt / fitsUint / fitsSizeT matches GMP`
- `Mpz.getInt / getUint / getSizeT / getLimb matches GMP`
- `Mpz.toString / setStr matches GMP`
- `Mpz.log2 matches GMP`
- `Mpz.bitCountAbs matches GMP`
- `Mpz.swap exchanges values`

The command is intentionally quiet on success, so the relevant transcript is:

```text
$ cd /Users/davirian/dev/active/lean4/zig-backend && zig build test
exit: 0
stdout: (silent success)
stderr: (silent success)
```

The Nat/Int Layer B/C Zig-side regression tests in the same `zig build test`
step also stayed green, including:

- `lean_alloc_mpz initializes LeanMPZ header and zero payload`
- `lean_cstr_to_nat uses scalar and big results at the Nat boundary`
- `nat arithmetic part 1 canonicalizes small and big results`
- `nat arithmetic part 2 zero-divisor and rc paths match object.cpp`
- `nat compare and bitwise match expected mixed-path semantics`
- `nat shift pow gcd log2 preserve rc discipline`
- `int constructors round-trip signs and boundaries`
- `int arithmetic part 1 randomized stress balances mpz allocations`
- `int division family zero-divisor and rc paths mirror object.cpp`
- `signed width conversions use two's-complement low bits`

### Layer B/C differential harness (`zig build bignum-diff`)

The dedicated bignum differential harness is the strongest end-to-end M4b
comparison because it checks both canonical workloads and randomized per-op
batches against the reference GMP binary.

Transcript:

```text
$ cd /Users/davirian/dev/active/lean4/zig-backend && zig build bignum-diff
bignum-diff: canonical=5 randomized_ops=13 total_cases=1664 mismatches=0 leaks=0
exit: 0
```

The recorded `tests/bignum-smoke/results.json` summary is:

```json
{
  "seed": "0x5eedcafe1234abcd",
  "allocator": { "alloc": 2103, "free": 2103, "net": 0 },
  "ops": {
    "add": { "pass": 128, "total": 128 },
    "sub": { "pass": 128, "total": 128 },
    "mul": { "pass": 128, "total": 128 },
    "div": { "pass": 128, "total": 128 },
    "div_exact": { "pass": 128, "total": 128 },
    "mod": { "pass": 128, "total": 128 },
    "ediv": { "pass": 128, "total": 128 },
    "emod": { "pass": 128, "total": 128 },
    "neg": { "pass": 128, "total": 128 },
    "eq": { "pass": 128, "total": 128 },
    "le": { "pass": 128, "total": 128 },
    "lt": { "pass": 128, "total": 128 },
    "nonneg": { "pass": 128, "total": 128 }
  }
}
```

That gives M4 the desired comparison points:

- **canonical workloads:** `2^100`, `1000!`, large gcd, mixed-sign div-family,
  string round-trip,
- **randomized workloads:** 13 operation families × 128 cases,
- **allocator gate:** zero net `LeanMPZ` leaks in the Zig-backed binary.

### EmitZig vs EmitC bignum smoke transcript

`bash tests/emitzig-smoke/bignum/run.sh` exits `0`, verifies that the emitted
Zig file contains the expected bignum externs/helpers, builds the Zig object,
links it against the split runtime, confirms no unresolved bignum externs
remain, and then compares the EmitZig and EmitC binaries byte-for-byte.

Shared stdout transcript (both binaries matched this exactly):

```text
36893488147419103811
18446744073709552072
340282366920938480286805202654879493184
18446744073709552404
1
false
true
true
489303872
489303872
```

The run also proved the helper/linkage side of M4c-A by printing the bignum
symbols found in the emitted Zig source, including:

- `lean_nat_big_succ`
- `lean_nat_big_add`
- `lean_nat_big_sub`
- `lean_nat_big_mul`
- `lean_nat_big_div`
- `lean_nat_big_mod`
- `lean_nat_big_eq`
- `lean_nat_big_le`
- `lean_nat_big_lt`
- `lean_cstr_to_nat`
- `lean_big_uint64_to_nat`
- `lean_uint32_of_big_nat`
- `lean_uint64_of_big_nat`

## Compactor cross-archive verification

The compactor story is intentionally split into two claims:

1. **what M4 proves:** header-prefix compatibility for Zig-allocated `LeanMPZ`
   objects and continued presence of the C++ compactor consumer;
2. **what M4 explicitly does not prove:** payload-equivalent round-tripping of
   the Zig `Mpz` layout through the old C++ compactor serializer/deserializer.

### Verification record

```text
$ cd /Users/davirian/dev/active/lean4/zig-backend && zig build test-abi
INFO: LeanMPZ compactor payload mismatch (zig=48, cpp=32); header-prefix compatibility only
panic: PASS (exited non-zero and printed 'boom' to stderr)
BX1.uint_variants OK
exit: 0
```

```text
$ nm -gU /Users/davirian/dev/active/lean4/zig-backend/zig-out/lib/libleanrt_cpp_partial.a | grep compact
__ZN4lean16object_compactor10insert_mpzEP11lean_object
_lean_compacted_region_free
_lean_compacted_region_is_memory_mapped
_lean_compacted_region_size
exit: 0
```

The meaning of the INFO line is the same one documented in
`docs/m4-bignum-feasibility.md`:

- `sizeof(MpzObject) == 48` on the Zig side,
- `sizeof(mpz_object) == 32` on the C++ side,
- the object header prefix is compatible,
- the payload layout is not.

So M4 exits with the right limited claim:

- **passed:** the existing C++ archive still owns the compactor entry points,
  still sees the expected header prefix, and the smoke fixture exits `0`;
- **deferred:** full payload-equivalent `insert_mpz` / deserializer support for
  the Zig `Mpz` layout.

## Reproducibility sweep

The required clean-state run was performed by **moving** the existing build
artifacts aside first:

```text
backup_root=/var/folders/ns/gzg902ps3ds9nzjwbsz_zk4w0000gn/T//m4-repro.1reogR
moved /Users/davirian/dev/active/lean4/zig-backend/src/EmitZig/.lake
moved /Users/davirian/dev/active/lean4/zig-backend/zig-out
moved /Users/davirian/dev/active/lean4/zig-backend/.zig-cache
```

Then the exact command sequence requested by the feature was rerun:

```text
$ cd /Users/davirian/dev/active/lean4/zig-backend/src/EmitZig && lake build
Build completed successfully (10 jobs).
exit: 0

$ cd /Users/davirian/dev/active/lean4/zig-backend && zig build
exit: 0

$ cd /Users/davirian/dev/active/lean4/zig-backend && zig build emitzig-smoke
exit: 0

$ cd /Users/davirian/dev/active/lean4/zig-backend && bash tests/emitzig-smoke/bignum/run.sh
exit: 0

$ cd /Users/davirian/dev/active/lean4/zig-backend && zig build emitzig-diff
exit: 0
```

End-of-run marker:

```text
repro_sweep=ok
```

So the M4 reproducibility claim is green: the shadow-tree Lake package, the
split runtime, the full EmitZig smoke bundle, the dedicated bignum EmitZig
smoke, and the EmitZig-vs-EmitC differential harness all rebuild cleanly after
the relevant caches are moved out of the way.

## Outer-repo cleanliness

Boundary check:

```text
$ git -C /Users/davirian/dev/active/lean4 status --porcelain -- ':!.gitignore' ':!zig-backend' ':!zig-backend/'
(empty)
exit: 0
```

That preserves the mission's bedrock invariant: the outer Lean repo still has
no changes beyond the already-allowed `.gitignore` exception and the mission's
owned `zig-backend/` subtree.

## Final command summary

The high-value closing commands for this report were:

| Command | Exit | Observation |
| --- | ---: | --- |
| `zig build && zig build test && zig build test-abi && bash tests/lean-smoke/run.sh && cd src/EmitZig && /Users/davirian/dev/active/lean4/build/release/stage1/bin/lake build && /Users/davirian/dev/active/lean4/build/release/stage1/bin/lake test` | 0 | Baseline full-validator sweep stayed green before the report closeout. |
| `zig build bignum-diff` | 0 | Printed `canonical=5 randomized_ops=13 total_cases=1664 mismatches=0 leaks=0`. |
| `bash tests/emitzig-smoke/bignum/run.sh` | 0 | EmitZig and EmitC stdout matched exactly; the emitted Zig file referenced the expected big-Nat helper surface. |
| `zig build test-abi` | 0 | Printed the expected LeanMPZ compactor INFO line and passed the smoke suite. |
| `git -C /Users/davirian/dev/active/lean4 status --porcelain -- ':!.gitignore' ':!zig-backend' ':!zig-backend/'` | 0 | Produced no output, confirming outer-repo cleanliness. |
| moved-cache reproducibility sweep (`lake build`, `zig build`, `zig build emitzig-smoke`, `bash tests/emitzig-smoke/bignum/run.sh`, `zig build emitzig-diff`) | 0 | Rebuilt successfully from a moved-away `.lake`, `zig-out`, and `.zig-cache` state. |

## Next steps for M5a / M5b

The M4 closeout leaves the bignum surface in a much better place, but it does
not change the larger mission ordering recorded in
`library/feasibility-m3-and-beyond.md`: **M5 must still be split.**

### M5a — task manager, thunks, heartbeat, and runtime-phase prerequisites

Concrete follow-ups:

1. move the task manager / promise / scheduling surface out of
   `libleanrt_cpp_partial.a`,
2. preserve the allocator + RC invariants already hardened by M3/M4,
3. keep `lean_run_main` initialization compatible with the shadow-tree EmitZig
   binaries now that M6 and M4c both rely on it,
4. add smoke coverage for `Task.spawn ... |>.get` before any broader IO work.

Why M5a comes first:

- `run_main` depends on task-manager initialization,
- the bignum path is now ready for bigger programs, but those bigger programs
  will immediately stress the runtime scheduler,
- moving IO first without stabilizing the task half would create a poor
  debugging surface for both EmitZig and the split runtime.

### M5b — IO, libuv, error decoding, and broader CLI/runtime interop

Concrete follow-ups:

1. move the required `lean_io_*` core surface out of delegated C++ ownership,
2. port the libuv/process-facing glue needed for real IO workloads,
3. keep the existing IO error constructor behavior compatible with the now-green
   M3/M4 runtime surface,
4. add smoke coverage for `IO.FS.readFile`, `IO.println`, and a small
   run-main-backed CLI program using the full split runtime.

Why M5b naturally follows M5a:

- the IO half depends on the task-manager initialization path,
- M4's bignum runtime is already sufficient for bigger numeric programs, so the
  next bottleneck is no longer arithmetic coverage but IO/runtime orchestration,
- EmitZig's next meaningful growth step after the current bignum smoke is
  “larger real programs”, and those programs need stable IO before they need
  another bignum pass.

## Bottom line

M4 closes with the full bignum runtime surface implemented, the EmitZig
bignum-coupling smoke green, the differential harness green, the compactor
header-prefix contract preserved, the clean-state rebuild sweep green, and all
previously sealed M1/M2/M3/M6/P1 assertions still passed. The remaining known
gap is not public-symbol coverage; it is the still-deferred payload-equivalent
compactor rewrite needed for a future all-Zig `Mpz` promotion.
