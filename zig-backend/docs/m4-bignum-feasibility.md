# M4 bignum feasibility

This note records the M4c feasibility pass for replacing Lean's `lean::mpz`/libgmp path with the Zig Layer A implementation in `zig-backend/src/mpz_zig.zig`, which is built on `std.math.big.int.Managed`.

Status summary from the readiness check:

- **Coverage:** 45 / 45 `lean::mpz`-relevant GMP entry points are accounted for.
- **Breakdown:** **34 present**, **11 partial**, **0 absent**.
- **Perf headline:** addition and 256-bit multiplication are close enough to be interesting, but division/gcd and 4096-bit arithmetic are still materially behind libgmp.
- **ABI/compactor headline:** runtime object-header compatibility is proven, but payload-equivalent compactor round-tripping is not.

## std.math.big.int API surface vs lean::mpz

Rubric used below:

- **present** = `std.math.big.int` already exposes the required semantics directly, or the wrapper maps to a single obvious std call.
- **partial** = Lean can be implemented today, but only with a shim/combo helper, internal metadata access, or a semantic fixup.
- **absent** = no reasonable mapping without a new implementation. There are **0** such rows in the current readiness set.

The table is the 45/45 readiness-check matrix, sourced from `src/runtime/mpz.{h,cpp}` and `zig-backend/src/mpz_zig.zig`.

| GMP / `lean::mpz` surface | `std.math.big.int` mapping | Status | Note |
| --- | --- | --- | --- |
| `mpz_init` | `Managed.init` | present | Direct empty-init. |
| `mpz_init_set` | `Managed.init` + `copy` / `initSet` | present | No semantic gap. |
| `mpz_init_set_str` | `Managed.init` + `setString` | present | Two-step init, same behavior for Lean's bases. |
| `mpz_init_set_ui` | `Managed.initSet(u64)` | present | Direct scalar constructor. |
| `mpz_init_set_si` | `Managed.initSet(i64)` | present | Direct scalar constructor. |
| `mpz_set` | `Managed.copy` | present | Direct copy into existing storage. |
| `mpz_set_str` | `Managed.setString` | present | Direct parse path. |
| `mpz_set_ui` | `Managed.set(u64)` | present | Direct set. |
| `mpz_set_si` | `Managed.set(i64)` | present | Direct set. |
| `mpz_swap` | `Managed.swap` | present | Direct swap. |
| `mpz_clear` | `Managed.deinit` | present | Direct teardown. |
| `mpz_sgn` | `Const.eqlZero` + `Managed.isPositive` | present | Wrapper-level sign helper. |
| `mpz_fits_sint_p` | `Managed.fits(i64)` | present | Direct fit query. |
| `mpz_fits_uint_p` | `Managed.fits(u64)` | present | Direct fit query. |
| `mpz_size` | `Managed.len()` | partial | Uses limb metadata rather than a dedicated public GMP-style API. |
| `mpz_get_si` | `Managed.toInt(i64)` | present | Direct conversion. |
| `mpz_get_ui` | `Managed.toInt(u64)` | present | Direct conversion. |
| `mpz_getlimbn` | `managed.limbs[index]` | present | Direct limb access in the wrapper. |
| `mpz_cmp` | `Managed.order` | present | Direct comparison. |
| `mpz_cmp_ui` | `Const.orderAgainstScalar(u64)` | present | Direct scalar comparison. |
| `mpz_cmp_si` | `Const.orderAgainstScalar(i64)` | present | Direct scalar comparison. |
| `mpz_add` | `Managed.add` | present | Direct add. |
| `mpz_add_ui` | temp scalar + `Managed.add` | partial | Needs a scalar helper/fast path rather than a single std call. |
| `mpz_sub` | `Managed.sub` | present | Direct subtract. |
| `mpz_sub_ui` | temp scalar + `Managed.sub` | partial | Same scalar-helper issue as `add_ui`. |
| `mpz_mul` | `Managed.mul` | present | Direct multiply. |
| `mpz_mul_ui` | temp scalar + `Managed.mul` | partial | No dedicated unsigned-scalar multiply entry point. |
| `mpz_mul_si` | sign split + scalar multiply + `negate` | partial | Same, plus signed fixup. |
| `mpz_divexact` | `Managed.divTrunc` + zero-remainder precondition | partial | Correct today, but not a dedicated exact-division specialization. |
| `mpz_tdiv_qr` | `Managed.divTrunc` | present | Direct quotient/remainder trunc division. |
| `mpz_tdiv_r` | `Managed.divTrunc` remainder out-param | present | Direct remainder path. |
| `mpz_tdiv_q` | `Managed.divTrunc` quotient out-param | present | Direct quotient path. |
| `mpz_tdiv_q_ui` | temp scalar divisor + `Managed.divTrunc` | partial | Needs scalar helper for the divisor. |
| `mpz_pow_ui` | `Managed.pow` | partial | Works, but std currently caps the exponent at `u32`. |
| `mpz_sizeinbase` | `bitCountAbs` / `toString(base)` derived | partial | Lean uses base-2 log sizing and decimal formatting; no single generic API. |
| `mpz_and` | two's-complement bridge + bytewise `&` | present | Implemented in `Mpz.bitAnd`; semantics covered. |
| `mpz_ior` | two's-complement bridge + bytewise `\|` | present | Implemented in `Mpz.bitOr`. |
| `mpz_xor` | two's-complement bridge + bytewise `^` | present | Implemented in `Mpz.bitXor`. |
| `mpz_mul_2exp` | `Managed.shiftLeft` | present | Direct shift-left. |
| `mpz_tdiv_q_2exp` | `Managed.shiftRight` | partial | Direct for non-negative values; negative truncate-to-zero needs a shim if exposed. |
| `mpz_fdiv_r_2exp` | `modPow2` / `smodPow2` helper | partial | Implemented via quotient/recompose logic, not a single std op. |
| `mpz_fdiv_q_2exp` | floor-shift helper | partial | Especially important for negative inputs; needs explicit floor semantics. |
| `mpz_gcd` | `Managed.gcd` | present | Direct gcd after capacity reservation. |
| `mpz_get_str` | `Managed.toString` | present | Direct string conversion. |
| `mpz_neg` | `Managed.negate` | present | Direct sign flip. |

The net result is that the **surface is complete enough to implement Lean today**, but the last 11 rows are exactly where the wrapper stops being a straightforward API rename and starts carrying Lean-specific compatibility logic.

## perf measurements

Methodology:

- Host: the mission's Apple Silicon macOS machine.
- Date: 2026-05-21.
- Zig side: temporary `zig run -O ReleaseFast` benchmark over `std.math.big.int.Managed`.
- GMP side: temporary `cc -O3 ... -lgmp` benchmark over raw `mpz_*`.
- Operand generation: deterministic hex patterns; add/mul/gcd use two positive operands at the target width; division uses a **2×-width dividend** and a target-width divisor so quotient work is non-trivial.
- Timed ops: `add`, `mul`, truncating `div`, `gcd`.
- Scope: pure big-int substrate cost only; this excludes `lean_object` allocation/RC overhead and excludes compactor serialization.

### Summary table

| Width | Op | Zig `std.math.big.int` ns/op | libgmp ns/op | Zig / GMP |
| --- | --- | ---: | ---: | ---: |
| ~64-bit | add | 6.8 | 6.2 | 1.10× |
| ~64-bit | mul | 12.7 | 6.3 | 2.02× |
| ~64-bit | div | 43.1 | 12.4 | 3.48× |
| ~64-bit | gcd | 827.8 | 53.0 | 15.62× |
| ~256-bit | add | 8.0 | 5.7 | 1.40× |
| ~256-bit | mul | 24.2 | 17.5 | 1.38× |
| ~256-bit | div | 118.2 | 45.0 | 2.63× |
| ~256-bit | gcd | 4733.7 | 619.7 | 7.64× |
| ~4096-bit | add | 105.6 | 15.6 | 6.77× |
| ~4096-bit | mul | 3507.8 | 892.8 | 3.93× |
| ~4096-bit | div | 9168.2 | 1371.8 | 6.68× |
| ~4096-bit | gcd | 15562.5 | 1178.2 | 13.21× |

### Readout

- **Add** is encouraging at 64/256 bits, but the 4096-bit result is a clear warning that GMP's limb kernels still dominate larger widths.
- **Mul** is close enough at 256 bits to keep the Zig path viable for correctness-first work, but it is still ~4× slower at 4096 bits.
- **Div** is consistently slower; the gap widens again at 4096 bits.
- **Gcd** is the clearest blocker for a blind promotion: it is **7.6× to 15.6×** slower across these runs.

### Raw transcripts

```text
benchmark=std.math.big.int.Managed
add bits=64 iterations=300000 ns_per_op=6.8
mul bits=64 iterations=200000 ns_per_op=12.7
div bits=64 iterations=120000 ns_per_op=43.1
gcd bits=64 iterations=100000 ns_per_op=827.8
add bits=256 iterations=150000 ns_per_op=8.0
mul bits=256 iterations=80000 ns_per_op=24.2
div bits=256 iterations=60000 ns_per_op=118.2
gcd bits=256 iterations=40000 ns_per_op=4733.7
add bits=4096 iterations=8000 ns_per_op=105.6
mul bits=4096 iterations=1500 ns_per_op=3507.8
div bits=4096 iterations=800 ns_per_op=9168.2
gcd bits=4096 iterations=300 ns_per_op=15562.5
```

```text
benchmark=libgmp
add bits=64 iterations=300000 ns_per_op=6.2
mul bits=64 iterations=200000 ns_per_op=6.3
div bits=64 iterations=120000 ns_per_op=12.4
gcd bits=64 iterations=100000 ns_per_op=53.0
add bits=256 iterations=150000 ns_per_op=5.7
mul bits=256 iterations=80000 ns_per_op=17.5
div bits=256 iterations=60000 ns_per_op=45.0
gcd bits=256 iterations=40000 ns_per_op=619.7
add bits=4096 iterations=8000 ns_per_op=15.6
mul bits=4096 iterations=1500 ns_per_op=892.8
div bits=4096 iterations=800 ns_per_op=1371.8
gcd bits=4096 iterations=300 ns_per_op=1178.2
```

## gaps identified

These are the **11 combo/shim cases** that keep the coverage table at "complete, but not frictionless". Each one already has a plausible strategy; none is a correctness blocker by itself.

| Gap case | Why it is not a drop-in std call | Current / proposed shim strategy |
| --- | --- | --- |
| `addScalar` | GMP exposes `mpz_add_ui`; `Managed` is big-int-to-big-int oriented. | Materialize a tiny temp scalar `Mpz` (or later special-case one-limb values) and reuse `Managed.add`. |
| `subScalar` | Same issue for `mpz_sub_ui`; signed branches in `lean::mpz` flip to add when needed. | Temp scalar + branch on sign, mirroring the C++ wrapper's `operator-=(int)`. |
| `mulScalar` | `mpz_mul_ui` is scalar-specialized; std only gives generic multiply. | Keep the generic multiply for correctness now; add a one-limb specialization only if profiling justifies it. |
| `mulSignedScalar` | `mpz_mul_si` also folds sign handling into the op. | Split sign/magnitude, do `mulScalar`, then `negate` if needed. |
| `divScalar` | `mpz_tdiv_q_ui` is a specialized scalar-divisor fast path. | Convert the divisor to a one-limb `Mpz` and use `divTrunc`; promote to a dedicated helper only if division remains hot after M9. |
| `divexact-specialization` | `mpz_divexact` promises exact division and can skip generic remainder work. | Current wrapper does `divTruncQR` and ignores the zero remainder; keep that for now, add a fast exact path only if perf work moves forward. |
| Euclidean div/mod fixup | Lean's Int API needs `ediv`/`emod`, not only trunc division. | Keep the current `divTruncQR` + remainder-sign correction helper (`adjustEuclidean`) because it is clear and already tested. |
| Signed bitwise bridge | GMP natively handles signed infinite-width bitwise ops; `Managed` does not expose that shape directly. | Continue using the current two's-complement byte-buffer bridge in `Mpz.bitAnd` / `bitOr` / `bitXor`. |
| `tdiv_q_2exp` on negatives | `shiftRight` naturally wants floor semantics; GMP's `tdiv` wants truncate-toward-zero. | For Nat this is irrelevant; if exposed for Int, add a negative-input fixup when low bits are discarded. |
| `fdiv_q_2exp` / `fdiv_r_2exp` on negatives | Lean's width-casts and `mod8/16/32/64` rely on floor-division-by-`2^k` behavior. | Keep `modPow2` / `smodPow2` helpers and an explicit floor-shift helper so negative semantics stay GMP-compatible. |
| `pow` exponent `u32` cap | `Managed.pow` currently takes `u32`, which is narrower than an arbitrary Lean Nat exponent. | Preserve the existing Layer B panic guard (`Nat.pow exponent is too big` / `Nat.shiftl exponent is too big`) and defer wider-exponent support unless M9 explicitly needs it. |

The practical read is: **the gap set is manageable, but it is not zero-cost**. Promotion is mostly blocked by performance and cross-archive object semantics, not by missing arithmetic correctness.

## allocator strategy comparison

| Aspect | GMP / `lean::mpz` today | Zig `Allocator` + `LeanMPZ` today |
| --- | --- | --- |
| Object header | `mpz_object` in the C++ runtime | `MpzObject` in `zig-backend/src/runtime/lean_object.zig` |
| Inline payload | GMP's `mpz_t` metadata inside the object | Zig's `Mpz { managed: big_int.Managed }` inside the object |
| Inline object size | `sizeof(mpz_object) == 32` | `sizeof(MpzObject) == 48` |
| Limb-buffer owner | GMP allocator / GMP internals | `std.heap.c_allocator` through `Managed` |
| Growth policy | GMP grows limbs with its own tuned heuristics | `Managed.ensureCapacity` / allocator-driven growth |
| Free path | C++ object teardown clears `mpz_t` | `lean_free_object` detects `LeanMPZ`, calls `mpzValue(...).deinit()`, then frees the outer object |
| Coupling to Lean RC | Mostly opaque to Lean; RC owns the wrapper object | Explicitly tied to `lean_dec` because the object free path must dispatch `Managed.deinit()` before `free` |

The current Zig path is attractive because ownership is explicit: `lean_alloc_mpz` allocates the outer `MpzObject`, `Managed` owns the limb buffer, and `lean_free_object` in `src/runtime/alloc.zig` does the final dispatch back into `Managed.deinit()`. That is a much simpler story to reason about than "Lean object points to GMP-managed internals somewhere else".

The downside is the compactor contract. The M4a-F2 smoke fixture proved only header-prefix compatibility, not payload equivalence:

`INFO: LeanMPZ compactor payload mismatch (zig=48, cpp=32); header-prefix compatibility only`

That line comes directly from `tests/abi-smoke/mpz_alloc.c`, and it matters. The existing C++ compactor logic still assumes the C++ `mpz_object` payload layout. Reimplementing `compact.cpp::insert_mpz` and its deserializer against the Zig `Mpz` layout is the prerequisite for full payload-equivalent compactor round-tripping. Unless the project chooses to promote the Zig path aggressively, that work should stay **deferred to M9**.

Allocator conclusion:

- **Correctness:** acceptable today for normal runtime ownership.
- **Payload-equivalent compactor compatibility:** **not** acceptable today.
- **Operational trade-off:** Zig's ownership model is cleaner for RC/finalization, but GMP still wins on mature growth heuristics and on not having to touch the compactor yet.

## M9 recommendation

**Recommendation: hybrid.**

Concretely:

1. **Keep the Zig Layer A implementation alive and tested** as the correctness/reference path.
2. **Do not make it the only default bignum engine yet** for the general runtime/toolchain.
3. **Use M9 to decide promotion only after two follow-ups land:**
   - compactor payload support (`insert_mpz` + deserializer rewritten for Zig `Mpz`);
   - a second perf pass focused on 4096-bit `mul`/`div`/`gcd`, where the current gap is still too large.

Why hybrid instead of immediate promote:

- The coverage story is good: **45/45** relevant operations are covered, with **0 absent** rows.
- The shim story is manageable: the 11 partial/combo cases are understandable engineering, not research problems.
- The **performance story is not yet promotion-grade**. At 256 bits the Zig path is plausible; at 4096 bits it is still **3.9× to 13.2×** slower on the measured ops, and gcd is the clearest warning.
- The **compactor payload mismatch is a real architectural blocker** for "drop in and forget about it" replacement.

So the M9 decision should be:

- **promote** only if compactor support is rewritten and large-width perf is materially improved;
- **defer** only if the team decides big-int perf dominates all other goals;
- **hybrid (recommended)** if the goal is to keep moving the Zig backend forward without taking unnecessary regression risk in one step.

In other words: **the feasibility verdict is positive for correctness, mixed for performance, and not yet ready for unconditional default promotion.**
