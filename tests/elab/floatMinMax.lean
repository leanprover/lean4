/-!
Checks that `Float.minimum`, `Float.maximum`, `Float.minimumNumber`, `Float.maximumNumber` and
their `Float32` counterparts implement the IEEE 754-2019 operations `minimum`, `maximum`,
`minimumNumber` and `maximumNumber`: all order `-0.0` below `0.0`, `minimum` and `maximum`
propagate `NaN` from either operand, and the `Number` variants return the other operand instead.
All eight functions are opaque, so only the compiled implementation is checked (`#guard`).
Propositional equality on `Float` and `Float32` compares bit patterns (with all `NaN`s identified),
so `= -0.0` below really checks the sign of the result, unlike `==`.
-/

/-- All pairs `(a, b)` where `a` occurs at or before `b` in the list. -/
def pairsLe {α : Type} : List α → List (α × α)
  | [] => []
  | x :: xs => (x :: xs).map (x, ·) ++ pairsLe xs

/-! ## `Float` -/

-- Sanity check for the technique: `=` tells the two zeros apart.
#guard ¬ ((0.0 : Float) = -0.0)

/-- The smallest positive subnormal `Float`. -/
def minSubnormal : Float := Float.ofBits 1
/-- The largest finite `Float`. -/
def maxFinite : Float := Float.ofBits 0x7FEFFFFFFFFFFFFF

/-! ### Ordered operands -/

#guard Float.minimum 1.0 2.0 = 1.0
#guard Float.minimum 2.0 1.0 = 1.0
#guard Float.minimum (-1.0) 1.0 = -1.0
#guard Float.minimum 3.0 3.0 = 3.0
#guard Float.minimum minSubnormal 0.0 = 0.0
#guard Float.minimum (-minSubnormal) 0.0 = -minSubnormal
#guard Float.minimum maxFinite Float.inf = maxFinite
#guard Float.minimum (-Float.inf) (-maxFinite) = -Float.inf

#guard Float.maximum 1.0 2.0 = 2.0
#guard Float.maximum 2.0 1.0 = 2.0
#guard Float.maximum (-1.0) 1.0 = 1.0
#guard Float.maximum 3.0 3.0 = 3.0
#guard Float.maximum minSubnormal 0.0 = minSubnormal
#guard Float.maximum (-minSubnormal) 0.0 = 0.0
#guard Float.maximum maxFinite Float.inf = Float.inf
#guard Float.maximum (-Float.inf) (-maxFinite) = -maxFinite

#guard Float.minimumNumber 1.0 2.0 = 1.0
#guard Float.minimumNumber 2.0 1.0 = 1.0
#guard Float.minimumNumber (-1.0) 1.0 = -1.0
#guard Float.minimumNumber 3.0 3.0 = 3.0
#guard Float.minimumNumber minSubnormal 0.0 = 0.0
#guard Float.minimumNumber (-minSubnormal) 0.0 = -minSubnormal
#guard Float.minimumNumber maxFinite Float.inf = maxFinite
#guard Float.minimumNumber (-Float.inf) (-maxFinite) = -Float.inf

#guard Float.maximumNumber 1.0 2.0 = 2.0
#guard Float.maximumNumber 2.0 1.0 = 2.0
#guard Float.maximumNumber (-1.0) 1.0 = 1.0
#guard Float.maximumNumber 3.0 3.0 = 3.0
#guard Float.maximumNumber minSubnormal 0.0 = minSubnormal
#guard Float.maximumNumber (-minSubnormal) 0.0 = 0.0
#guard Float.maximumNumber maxFinite Float.inf = Float.inf
#guard Float.maximumNumber (-Float.inf) (-maxFinite) = -maxFinite

/-! ### Signed zeros: `-0.0 < 0.0` -/

#guard Float.minimum 0.0 (-0.0) = -0.0
#guard Float.minimum (-0.0) 0.0 = -0.0
#guard Float.minimum 0.0 0.0 = 0.0
#guard Float.minimum (-0.0) (-0.0) = -0.0

#guard Float.maximum 0.0 (-0.0) = 0.0
#guard Float.maximum (-0.0) 0.0 = 0.0
#guard Float.maximum 0.0 0.0 = 0.0
#guard Float.maximum (-0.0) (-0.0) = -0.0

#guard Float.minimumNumber 0.0 (-0.0) = -0.0
#guard Float.minimumNumber (-0.0) 0.0 = -0.0
#guard Float.minimumNumber 0.0 0.0 = 0.0
#guard Float.minimumNumber (-0.0) (-0.0) = -0.0

#guard Float.maximumNumber 0.0 (-0.0) = 0.0
#guard Float.maximumNumber (-0.0) 0.0 = 0.0
#guard Float.maximumNumber 0.0 0.0 = 0.0
#guard Float.maximumNumber (-0.0) (-0.0) = -0.0

/-! ### Infinities -/

#guard Float.minimum (-Float.inf) 1.0 = -Float.inf
#guard Float.minimum 1.0 (-Float.inf) = -Float.inf
#guard Float.minimum Float.inf 1.0 = 1.0
#guard Float.minimum Float.inf (-Float.inf) = -Float.inf
#guard Float.minimum Float.inf Float.inf = Float.inf

#guard Float.maximum (-Float.inf) 1.0 = 1.0
#guard Float.maximum 1.0 (-Float.inf) = 1.0
#guard Float.maximum Float.inf 1.0 = Float.inf
#guard Float.maximum Float.inf (-Float.inf) = Float.inf
#guard Float.maximum Float.inf Float.inf = Float.inf

#guard Float.minimumNumber (-Float.inf) 1.0 = -Float.inf
#guard Float.minimumNumber 1.0 (-Float.inf) = -Float.inf
#guard Float.minimumNumber Float.inf 1.0 = 1.0
#guard Float.minimumNumber Float.inf (-Float.inf) = -Float.inf
#guard Float.minimumNumber Float.inf Float.inf = Float.inf

#guard Float.maximumNumber (-Float.inf) 1.0 = 1.0
#guard Float.maximumNumber 1.0 (-Float.inf) = 1.0
#guard Float.maximumNumber Float.inf 1.0 = Float.inf
#guard Float.maximumNumber Float.inf (-Float.inf) = Float.inf
#guard Float.maximumNumber Float.inf Float.inf = Float.inf

/-! ### `NaN`: `minimum` and `maximum` propagate it, the `Number` variants prefer the number -/

#guard (Float.minimum Float.nan 1.0).isNaN
#guard (Float.minimum 1.0 Float.nan).isNaN
#guard (Float.minimum Float.nan Float.nan).isNaN
#guard (Float.minimum Float.nan (-Float.inf)).isNaN
#guard (Float.minimum (-Float.inf) Float.nan).isNaN
#guard (Float.minimum Float.nan (-0.0)).isNaN
-- A `NaN` produced by arithmetic (typically with the sign bit set) behaves the same.
#guard (Float.minimum (0.0 / 0.0) 1.0).isNaN

#guard (Float.maximum Float.nan 1.0).isNaN
#guard (Float.maximum 1.0 Float.nan).isNaN
#guard (Float.maximum Float.nan Float.nan).isNaN
#guard (Float.maximum Float.nan Float.inf).isNaN
#guard (Float.maximum Float.inf Float.nan).isNaN
#guard (Float.maximum Float.nan 0.0).isNaN
#guard (Float.maximum (0.0 / 0.0) 1.0).isNaN

#guard Float.minimumNumber Float.nan 1.0 = 1.0
#guard Float.minimumNumber 1.0 Float.nan = 1.0
#guard (Float.minimumNumber Float.nan Float.nan).isNaN
#guard Float.minimumNumber Float.nan (-Float.inf) = -Float.inf
#guard Float.minimumNumber Float.nan Float.inf = Float.inf
#guard Float.minimumNumber Float.inf Float.nan = Float.inf
-- The sign of a zero survives the `NaN` being dropped.
#guard Float.minimumNumber Float.nan (-0.0) = -0.0
#guard Float.minimumNumber (-0.0) Float.nan = -0.0
#guard Float.minimumNumber Float.nan 0.0 = 0.0
#guard Float.minimumNumber (0.0 / 0.0) 1.0 = 1.0

#guard Float.maximumNumber Float.nan 1.0 = 1.0
#guard Float.maximumNumber 1.0 Float.nan = 1.0
#guard (Float.maximumNumber Float.nan Float.nan).isNaN
#guard Float.maximumNumber Float.nan (-Float.inf) = -Float.inf
#guard Float.maximumNumber Float.nan Float.inf = Float.inf
#guard Float.maximumNumber (-Float.inf) Float.nan = -Float.inf
#guard Float.maximumNumber Float.nan (-0.0) = -0.0
#guard Float.maximumNumber (-0.0) Float.nan = -0.0
#guard Float.maximumNumber Float.nan 0.0 = 0.0
#guard Float.maximumNumber (0.0 / 0.0) 1.0 = 1.0

/-! ### Exhaustive sweep over a sorted list of non-`NaN` values -/

/-- Test values in ascending order, with `-0.0` before `0.0` as the operations order them. -/
def sorted : List Float :=
  [-Float.inf, -maxFinite, -1.0, -minSubnormal, -0.0, 0.0,
    minSubnormal, 1.0, maxFinite, Float.inf]

-- For `a ≤ b` in list order the minimum is `a` and the maximum is `b` bit-for-bit, in either
-- argument order.
#guard (pairsLe sorted).all fun (a, b) => Float.minimum a b = a && Float.minimum b a = a
#guard (pairsLe sorted).all fun (a, b) => Float.maximum a b = b && Float.maximum b a = b
#guard (pairsLe sorted).all fun (a, b) =>
  Float.minimumNumber a b = a && Float.minimumNumber b a = a
#guard (pairsLe sorted).all fun (a, b) =>
  Float.maximumNumber a b = b && Float.maximumNumber b a = b

-- `NaN` in either position: propagated by `minimum` and `maximum`, dropped by the `Number`
-- variants.
#guard sorted.all fun a =>
  (Float.minimum Float.nan a).isNaN && (Float.minimum a Float.nan).isNaN
#guard sorted.all fun a =>
  (Float.maximum Float.nan a).isNaN && (Float.maximum a Float.nan).isNaN
#guard sorted.all fun a =>
  Float.minimumNumber Float.nan a = a && Float.minimumNumber a Float.nan = a
#guard sorted.all fun a =>
  Float.maximumNumber Float.nan a = a && Float.maximumNumber a Float.nan = a

/-! ## `Float32` -/

-- Sanity check for the technique: `=` tells the two zeros apart.
#guard ¬ ((0.0 : Float32) = -0.0)

/-- The smallest positive subnormal `Float32`. -/
def minSubnormal32 : Float32 := Float32.ofBits 1
/-- The largest finite `Float32`. -/
def maxFinite32 : Float32 := Float32.ofBits 0x7F7FFFFF

/-! ### Ordered operands -/

#guard Float32.minimum 1.0 2.0 = 1.0
#guard Float32.minimum 2.0 1.0 = 1.0
#guard Float32.minimum (-1.0) 1.0 = -1.0
#guard Float32.minimum 3.0 3.0 = 3.0
#guard Float32.minimum minSubnormal32 0.0 = 0.0
#guard Float32.minimum (-minSubnormal32) 0.0 = -minSubnormal32
#guard Float32.minimum maxFinite32 Float32.inf = maxFinite32
#guard Float32.minimum (-Float32.inf) (-maxFinite32) = -Float32.inf

#guard Float32.maximum 1.0 2.0 = 2.0
#guard Float32.maximum 2.0 1.0 = 2.0
#guard Float32.maximum (-1.0) 1.0 = 1.0
#guard Float32.maximum 3.0 3.0 = 3.0
#guard Float32.maximum minSubnormal32 0.0 = minSubnormal32
#guard Float32.maximum (-minSubnormal32) 0.0 = 0.0
#guard Float32.maximum maxFinite32 Float32.inf = Float32.inf
#guard Float32.maximum (-Float32.inf) (-maxFinite32) = -maxFinite32

#guard Float32.minimumNumber 1.0 2.0 = 1.0
#guard Float32.minimumNumber 2.0 1.0 = 1.0
#guard Float32.minimumNumber (-1.0) 1.0 = -1.0
#guard Float32.minimumNumber 3.0 3.0 = 3.0
#guard Float32.minimumNumber minSubnormal32 0.0 = 0.0
#guard Float32.minimumNumber (-minSubnormal32) 0.0 = -minSubnormal32
#guard Float32.minimumNumber maxFinite32 Float32.inf = maxFinite32
#guard Float32.minimumNumber (-Float32.inf) (-maxFinite32) = -Float32.inf

#guard Float32.maximumNumber 1.0 2.0 = 2.0
#guard Float32.maximumNumber 2.0 1.0 = 2.0
#guard Float32.maximumNumber (-1.0) 1.0 = 1.0
#guard Float32.maximumNumber 3.0 3.0 = 3.0
#guard Float32.maximumNumber minSubnormal32 0.0 = minSubnormal32
#guard Float32.maximumNumber (-minSubnormal32) 0.0 = 0.0
#guard Float32.maximumNumber maxFinite32 Float32.inf = Float32.inf
#guard Float32.maximumNumber (-Float32.inf) (-maxFinite32) = -maxFinite32

/-! ### Signed zeros: `-0.0 < 0.0` -/

#guard Float32.minimum 0.0 (-0.0) = -0.0
#guard Float32.minimum (-0.0) 0.0 = -0.0
#guard Float32.minimum 0.0 0.0 = 0.0
#guard Float32.minimum (-0.0) (-0.0) = -0.0

#guard Float32.maximum 0.0 (-0.0) = 0.0
#guard Float32.maximum (-0.0) 0.0 = 0.0
#guard Float32.maximum 0.0 0.0 = 0.0
#guard Float32.maximum (-0.0) (-0.0) = -0.0

#guard Float32.minimumNumber 0.0 (-0.0) = -0.0
#guard Float32.minimumNumber (-0.0) 0.0 = -0.0
#guard Float32.minimumNumber 0.0 0.0 = 0.0
#guard Float32.minimumNumber (-0.0) (-0.0) = -0.0

#guard Float32.maximumNumber 0.0 (-0.0) = 0.0
#guard Float32.maximumNumber (-0.0) 0.0 = 0.0
#guard Float32.maximumNumber 0.0 0.0 = 0.0
#guard Float32.maximumNumber (-0.0) (-0.0) = -0.0

/-! ### Infinities -/

#guard Float32.minimum (-Float32.inf) 1.0 = -Float32.inf
#guard Float32.minimum 1.0 (-Float32.inf) = -Float32.inf
#guard Float32.minimum Float32.inf 1.0 = 1.0
#guard Float32.minimum Float32.inf (-Float32.inf) = -Float32.inf
#guard Float32.minimum Float32.inf Float32.inf = Float32.inf

#guard Float32.maximum (-Float32.inf) 1.0 = 1.0
#guard Float32.maximum 1.0 (-Float32.inf) = 1.0
#guard Float32.maximum Float32.inf 1.0 = Float32.inf
#guard Float32.maximum Float32.inf (-Float32.inf) = Float32.inf
#guard Float32.maximum Float32.inf Float32.inf = Float32.inf

#guard Float32.minimumNumber (-Float32.inf) 1.0 = -Float32.inf
#guard Float32.minimumNumber 1.0 (-Float32.inf) = -Float32.inf
#guard Float32.minimumNumber Float32.inf 1.0 = 1.0
#guard Float32.minimumNumber Float32.inf (-Float32.inf) = -Float32.inf
#guard Float32.minimumNumber Float32.inf Float32.inf = Float32.inf

#guard Float32.maximumNumber (-Float32.inf) 1.0 = 1.0
#guard Float32.maximumNumber 1.0 (-Float32.inf) = 1.0
#guard Float32.maximumNumber Float32.inf 1.0 = Float32.inf
#guard Float32.maximumNumber Float32.inf (-Float32.inf) = Float32.inf
#guard Float32.maximumNumber Float32.inf Float32.inf = Float32.inf

/-! ### `NaN`: `minimum` and `maximum` propagate it, the `Number` variants prefer the number -/

#guard (Float32.minimum Float32.nan 1.0).isNaN
#guard (Float32.minimum 1.0 Float32.nan).isNaN
#guard (Float32.minimum Float32.nan Float32.nan).isNaN
#guard (Float32.minimum Float32.nan (-Float32.inf)).isNaN
#guard (Float32.minimum (-Float32.inf) Float32.nan).isNaN
#guard (Float32.minimum Float32.nan (-0.0)).isNaN
-- A `NaN` produced by arithmetic (typically with the sign bit set) behaves the same.
#guard (Float32.minimum (0.0 / 0.0) 1.0).isNaN

#guard (Float32.maximum Float32.nan 1.0).isNaN
#guard (Float32.maximum 1.0 Float32.nan).isNaN
#guard (Float32.maximum Float32.nan Float32.nan).isNaN
#guard (Float32.maximum Float32.nan Float32.inf).isNaN
#guard (Float32.maximum Float32.inf Float32.nan).isNaN
#guard (Float32.maximum Float32.nan 0.0).isNaN
#guard (Float32.maximum (0.0 / 0.0) 1.0).isNaN

#guard Float32.minimumNumber Float32.nan 1.0 = 1.0
#guard Float32.minimumNumber 1.0 Float32.nan = 1.0
#guard (Float32.minimumNumber Float32.nan Float32.nan).isNaN
#guard Float32.minimumNumber Float32.nan (-Float32.inf) = -Float32.inf
#guard Float32.minimumNumber Float32.nan Float32.inf = Float32.inf
#guard Float32.minimumNumber Float32.inf Float32.nan = Float32.inf
-- The sign of a zero survives the `NaN` being dropped.
#guard Float32.minimumNumber Float32.nan (-0.0) = -0.0
#guard Float32.minimumNumber (-0.0) Float32.nan = -0.0
#guard Float32.minimumNumber Float32.nan 0.0 = 0.0
#guard Float32.minimumNumber (0.0 / 0.0) 1.0 = 1.0

#guard Float32.maximumNumber Float32.nan 1.0 = 1.0
#guard Float32.maximumNumber 1.0 Float32.nan = 1.0
#guard (Float32.maximumNumber Float32.nan Float32.nan).isNaN
#guard Float32.maximumNumber Float32.nan (-Float32.inf) = -Float32.inf
#guard Float32.maximumNumber Float32.nan Float32.inf = Float32.inf
#guard Float32.maximumNumber (-Float32.inf) Float32.nan = -Float32.inf
#guard Float32.maximumNumber Float32.nan (-0.0) = -0.0
#guard Float32.maximumNumber (-0.0) Float32.nan = -0.0
#guard Float32.maximumNumber Float32.nan 0.0 = 0.0
#guard Float32.maximumNumber (0.0 / 0.0) 1.0 = 1.0

/-! ### Exhaustive sweep over a sorted list of non-`NaN` values -/

/-- Test values in ascending order, with `-0.0` before `0.0` as the operations order them. -/
def sorted32 : List Float32 :=
  [-Float32.inf, -maxFinite32, -1.0, -minSubnormal32, -0.0, 0.0,
    minSubnormal32, 1.0, maxFinite32, Float32.inf]

-- For `a ≤ b` in list order the minimum is `a` and the maximum is `b` bit-for-bit, in either
-- argument order.
#guard (pairsLe sorted32).all fun (a, b) => Float32.minimum a b = a && Float32.minimum b a = a
#guard (pairsLe sorted32).all fun (a, b) => Float32.maximum a b = b && Float32.maximum b a = b
#guard (pairsLe sorted32).all fun (a, b) =>
  Float32.minimumNumber a b = a && Float32.minimumNumber b a = a
#guard (pairsLe sorted32).all fun (a, b) =>
  Float32.maximumNumber a b = b && Float32.maximumNumber b a = b

-- `NaN` in either position: propagated by `minimum` and `maximum`, dropped by the `Number`
-- variants.
#guard sorted32.all fun a =>
  (Float32.minimum Float32.nan a).isNaN && (Float32.minimum a Float32.nan).isNaN
#guard sorted32.all fun a =>
  (Float32.maximum Float32.nan a).isNaN && (Float32.maximum a Float32.nan).isNaN
#guard sorted32.all fun a =>
  Float32.minimumNumber Float32.nan a = a && Float32.minimumNumber a Float32.nan = a
#guard sorted32.all fun a =>
  Float32.maximumNumber Float32.nan a = a && Float32.maximumNumber a Float32.nan = a
