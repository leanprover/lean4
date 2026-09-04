/-!
Tests for `Float.fma` and `Float32.fma`, which are backed by the logical float model.
Each fact is checked twice: in the kernel via the model (`by decide +kernel`) and with the
untrusted evaluator via the compiled C `fma`/`fmaf` (`#guard`), so the two must agree —
including on the cases that distinguish a fused multiply-add from a multiply followed by
an add.
-/

-- Exact arithmetic.
example : Float.fma 2.0 3.0 1.0 = 7.0 := by decide +kernel
#guard Float.fma 2.0 3.0 1.0 == 7.0
example : Float32.fma 2.0 3.0 1.0 = 7.0 := by decide +kernel
#guard Float32.fma 2.0 3.0 1.0 == 7.0

-- Single rounding: with `e = 2^-27`, `(1 + e)² = 1 + 2e + e²` needs 55 significand bits, so
-- `mul` rounds `e²` away while `fma` recovers it exactly.
example :
    let e : Float := 1.0 / 134217728.0
    Float.fma (1.0 + e) (1.0 + e) (-(1.0 + 2.0 * e)) = e * e := by decide +kernel
#guard
  let e : Float := 1.0 / 134217728.0
  Float.fma (1.0 + e) (1.0 + e) (-(1.0 + 2.0 * e)) == e * e
example :
    let e : Float := 1.0 / 134217728.0
    (1.0 + e) * (1.0 + e) - (1.0 + 2.0 * e) = 0.0 := by decide +kernel
#guard
  let e : Float := 1.0 / 134217728.0
  (1.0 + e) * (1.0 + e) - (1.0 + 2.0 * e) == 0.0

-- The same in `binary32`, with `e = 2^-12`.
example :
    let e : Float32 := 1.0 / 4096.0
    Float32.fma (1.0 + e) (1.0 + e) (-(1.0 + 2.0 * e)) = e * e := by decide +kernel
#guard
  let e : Float32 := 1.0 / 4096.0
  Float32.fma (1.0 + e) (1.0 + e) (-(1.0 + 2.0 * e)) == e * e

-- The exact product is never rounded on its own: a product that would overflow next to an
-- infinite `z` of the opposite sign still yields that infinity, where `mul` then `add` gives
-- `Inf - Inf = NaN`.
example : Float.fma 1e300 1e300 (-Float.inf) = -Float.inf := by decide +kernel
#guard Float.fma 1e300 1e300 (-Float.inf) == -Float.inf
example : (1e300 * 1e300 + (-Float.inf)).isNaN := by decide +kernel
#guard (1e300 * 1e300 + (-Float.inf)).isNaN

-- Zero-result signs. Exact cancellation gives `+0` (round-to-nearest addition rule).
example : (Float.fma 2.0 3.0 (-6.0)).toBits = 0 := by decide +kernel
#guard (Float.fma 2.0 3.0 (-6.0)).toBits == 0
-- A product that underflows to zero next to a zero `z` of the opposite sign keeps the
-- product's sign; computing `x * y + z` with two roundings gives `+0` here instead.
example : (Float.fma (-1e-200) 1e-200 0.0).toBits = 0x8000000000000000 := by decide +kernel
#guard (Float.fma (-1e-200) 1e-200 0.0).toBits == 0x8000000000000000
example : ((-1e-200) * 1e-200 + 0.0).toBits = 0 := by decide +kernel
#guard ((-1e-200) * 1e-200 + 0.0).toBits == 0
example : (Float32.fma (-1e-30) 1e-30 0.0).toBits = 0x80000000 := by decide +kernel
#guard (Float32.fma (-1e-30) 1e-30 0.0).toBits == 0x80000000
-- A positive underflowing product next to `-0` gives `+0`.
example : (Float.fma 1e-200 1e-200 (-0.0)).toBits = 0 := by decide +kernel
#guard (Float.fma 1e-200 1e-200 (-0.0)).toBits == 0
-- Exactly-zero products follow the addition rules for signed zeros.
example : (Float.fma (-0.0) 5.0 (-0.0)).toBits = 0x8000000000000000 := by decide +kernel
#guard (Float.fma (-0.0) 5.0 (-0.0)).toBits == 0x8000000000000000
example : (Float.fma (-0.0) 5.0 0.0).toBits = 0 := by decide +kernel
#guard (Float.fma (-0.0) 5.0 0.0).toBits == 0
example : Float.fma 0.0 5.0 3.0 = 3.0 := by decide +kernel
#guard Float.fma 0.0 5.0 3.0 == 3.0

-- Special values.
example : (Float.fma 0.0 Float.inf 1.0).isNaN := by decide +kernel
#guard (Float.fma 0.0 Float.inf 1.0).isNaN
example : (Float.fma Float.inf 1.0 (-Float.inf)).isNaN := by decide +kernel
#guard (Float.fma Float.inf 1.0 (-Float.inf)).isNaN
example : Float.fma Float.inf 2.0 (-1e300) = Float.inf := by decide +kernel
#guard Float.fma Float.inf 2.0 (-1e300) == Float.inf
example : Float.fma 2.0 3.0 Float.inf = Float.inf := by decide +kernel
#guard Float.fma 2.0 3.0 Float.inf == Float.inf
example : (Float.fma Float.nan 1.0 1.0).isNaN := by decide +kernel
#guard (Float.fma Float.nan 1.0 1.0).isNaN
example : (Float.fma 1.0 1.0 Float.nan).isNaN := by decide +kernel
#guard (Float.fma 1.0 1.0 Float.nan).isNaN
