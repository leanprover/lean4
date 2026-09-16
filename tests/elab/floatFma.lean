/-!
Checks that `Float.fma` and `Float32.fma` reduce in the kernel via the logical model
(`by decide +kernel`) and agree with the compiled C `fma`/`fmaf` (`#guard`), including on a
case that distinguishes a fused multiply-add from a multiply followed by an add. Broad
coverage comes from the Berkeley TestFloat vectors `f64_mulAdd`/`f32_mulAdd` checked by
`tests/pkg/float`, which cannot exercise kernel reduction.
-/

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

-- The same in `binary32`, with `e = 2^-12`.
example :
    let e : Float32 := 1.0 / 4096.0
    Float32.fma (1.0 + e) (1.0 + e) (-(1.0 + 2.0 * e)) = e * e := by decide +kernel
#guard
  let e : Float32 := 1.0 / 4096.0
  Float32.fma (1.0 + e) (1.0 + e) (-(1.0 + 2.0 * e)) == e * e

-- The exact product is never rounded on its own.
example : Float.fma 1e300 1e300 (-Float.inf) = -Float.inf := by decide +kernel
#guard Float.fma 1e300 1e300 (-Float.inf) == -Float.inf
example : (Float.fma 0.0 Float.inf 1.0).isNaN := by decide +kernel
#guard (Float.fma 0.0 Float.inf 1.0).isNaN
