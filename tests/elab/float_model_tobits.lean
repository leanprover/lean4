/-!
Checks that `Float.ofModel` and `Float.toModel` behave correctly at elaboration
time via `#guard`: the triangle relating the two `toBits` functions commutes
(`Float.toBits = Float.Model.toBits ∘ Float.toModel`), and round-tripping a
`Float` through its `Float.Model` reproduces it bit-for-bit.
-/

-- The `toBits` triangle commutes for a single value.
#guard (1.0 : Float).toBits == (1.0 : Float).toModel.toBits

-- `Float.ofModel ∘ Float.toModel = id`, bit-for-bit.
#guard (Float.ofModel (3.14 : Float).toModel).toBits == (3.14 : Float).toBits

-- Both properties hold across normals, signed zeroes, infinities, and `NaN`.
#guard [0.0, -0.0, 1.0, -1.0, 3.14, -2.5, 1e308, 1e-308, 1 / 0, -1 / 0, 0 / 0].all
  fun f => f.toBits == f.toModel.toBits && (Float.ofModel f.toModel).toBits == f.toBits
