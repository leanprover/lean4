/-!
Checks that `Float.minimum`, `Float.maximum`, `Float.minimumNumber`, `Float.maximumNumber` and
their `Float32` counterparts implement the IEEE 754-2019 operations `minimum`, `maximum`,
`minimumNumber` and `maximumNumber`: all order `-0.0` below `0.0`, `minimum` and `maximum`
propagate `NaN` from either operand, and the `Number` variants return the other operand instead.
Each function has a logical model in terms of `Float.Model` or `Float32.Model`, so `#test` checks
every claim twice: against the compiled implementation (`#guard`) and by kernel reduction of the
model (`by decide +kernel`).
Propositional equality on `Float` and `Float32` compares bit patterns (with all `NaN`s identified),
so `= -0.0` below really checks the sign of the result, unlike `==`.
-/

/-- Checks `t` with the compiled implementation and by kernel reduction of the logical model. -/
macro tk:"#test " t:term : command =>
  `(#guard%$tk $t
    example : $t := by decide +kernel)

/-- All pairs `(a, b)` where `a` occurs at or before `b` in the list. -/
def pairsLe {α : Type} : List α → List (α × α)
  | [] => []
  | x :: xs => (x :: xs).map (x, ·) ++ pairsLe xs

/-! ## `Float` -/

-- Sanity check for the technique: `=` tells the two zeros apart.
#test ¬ ((0.0 : Float) = -0.0)

/-- The smallest positive subnormal `Float`. -/
def minSubnormal : Float := Float.ofBits 1
/-- The largest finite `Float`. -/
def maxFinite : Float := Float.ofBits 0x7FEFFFFFFFFFFFFF

/-! ### Ordered operands -/

#test Float.minimum 1.0 2.0 = 1.0
#test Float.minimum 2.0 1.0 = 1.0
#test Float.minimum (-1.0) 1.0 = -1.0
#test Float.minimum 3.0 3.0 = 3.0
#test Float.minimum minSubnormal 0.0 = 0.0
#test Float.minimum (-minSubnormal) 0.0 = -minSubnormal
#test Float.minimum maxFinite Float.inf = maxFinite
#test Float.minimum (-Float.inf) (-maxFinite) = -Float.inf

#test Float.maximum 1.0 2.0 = 2.0
#test Float.maximum 2.0 1.0 = 2.0
#test Float.maximum (-1.0) 1.0 = 1.0
#test Float.maximum 3.0 3.0 = 3.0
#test Float.maximum minSubnormal 0.0 = minSubnormal
#test Float.maximum (-minSubnormal) 0.0 = 0.0
#test Float.maximum maxFinite Float.inf = Float.inf
#test Float.maximum (-Float.inf) (-maxFinite) = -maxFinite

#test Float.minimumNumber 1.0 2.0 = 1.0
#test Float.minimumNumber 2.0 1.0 = 1.0
#test Float.minimumNumber (-1.0) 1.0 = -1.0
#test Float.minimumNumber 3.0 3.0 = 3.0
#test Float.minimumNumber minSubnormal 0.0 = 0.0
#test Float.minimumNumber (-minSubnormal) 0.0 = -minSubnormal
#test Float.minimumNumber maxFinite Float.inf = maxFinite
#test Float.minimumNumber (-Float.inf) (-maxFinite) = -Float.inf

#test Float.maximumNumber 1.0 2.0 = 2.0
#test Float.maximumNumber 2.0 1.0 = 2.0
#test Float.maximumNumber (-1.0) 1.0 = 1.0
#test Float.maximumNumber 3.0 3.0 = 3.0
#test Float.maximumNumber minSubnormal 0.0 = minSubnormal
#test Float.maximumNumber (-minSubnormal) 0.0 = 0.0
#test Float.maximumNumber maxFinite Float.inf = Float.inf
#test Float.maximumNumber (-Float.inf) (-maxFinite) = -maxFinite

/-! ### Signed zeros: `-0.0 < 0.0` -/

#test Float.minimum 0.0 (-0.0) = -0.0
#test Float.minimum (-0.0) 0.0 = -0.0
#test Float.minimum 0.0 0.0 = 0.0
#test Float.minimum (-0.0) (-0.0) = -0.0

#test Float.maximum 0.0 (-0.0) = 0.0
#test Float.maximum (-0.0) 0.0 = 0.0
#test Float.maximum 0.0 0.0 = 0.0
#test Float.maximum (-0.0) (-0.0) = -0.0

#test Float.minimumNumber 0.0 (-0.0) = -0.0
#test Float.minimumNumber (-0.0) 0.0 = -0.0
#test Float.minimumNumber 0.0 0.0 = 0.0
#test Float.minimumNumber (-0.0) (-0.0) = -0.0

#test Float.maximumNumber 0.0 (-0.0) = 0.0
#test Float.maximumNumber (-0.0) 0.0 = 0.0
#test Float.maximumNumber 0.0 0.0 = 0.0
#test Float.maximumNumber (-0.0) (-0.0) = -0.0

/-! ### Infinities -/

#test Float.minimum (-Float.inf) 1.0 = -Float.inf
#test Float.minimum 1.0 (-Float.inf) = -Float.inf
#test Float.minimum Float.inf 1.0 = 1.0
#test Float.minimum Float.inf (-Float.inf) = -Float.inf
#test Float.minimum Float.inf Float.inf = Float.inf

#test Float.maximum (-Float.inf) 1.0 = 1.0
#test Float.maximum 1.0 (-Float.inf) = 1.0
#test Float.maximum Float.inf 1.0 = Float.inf
#test Float.maximum Float.inf (-Float.inf) = Float.inf
#test Float.maximum Float.inf Float.inf = Float.inf

#test Float.minimumNumber (-Float.inf) 1.0 = -Float.inf
#test Float.minimumNumber 1.0 (-Float.inf) = -Float.inf
#test Float.minimumNumber Float.inf 1.0 = 1.0
#test Float.minimumNumber Float.inf (-Float.inf) = -Float.inf
#test Float.minimumNumber Float.inf Float.inf = Float.inf

#test Float.maximumNumber (-Float.inf) 1.0 = 1.0
#test Float.maximumNumber 1.0 (-Float.inf) = 1.0
#test Float.maximumNumber Float.inf 1.0 = Float.inf
#test Float.maximumNumber Float.inf (-Float.inf) = Float.inf
#test Float.maximumNumber Float.inf Float.inf = Float.inf

/-! ### `NaN`: `minimum` and `maximum` propagate it, the `Number` variants prefer the number -/

#test (Float.minimum Float.nan 1.0).isNaN
#test (Float.minimum 1.0 Float.nan).isNaN
#test (Float.minimum Float.nan Float.nan).isNaN
#test (Float.minimum Float.nan (-Float.inf)).isNaN
#test (Float.minimum (-Float.inf) Float.nan).isNaN
#test (Float.minimum Float.nan (-0.0)).isNaN
-- A `NaN` produced by arithmetic (typically with the sign bit set) behaves the same.
#test (Float.minimum (0.0 / 0.0) 1.0).isNaN

#test (Float.maximum Float.nan 1.0).isNaN
#test (Float.maximum 1.0 Float.nan).isNaN
#test (Float.maximum Float.nan Float.nan).isNaN
#test (Float.maximum Float.nan Float.inf).isNaN
#test (Float.maximum Float.inf Float.nan).isNaN
#test (Float.maximum Float.nan 0.0).isNaN
#test (Float.maximum (0.0 / 0.0) 1.0).isNaN

#test Float.minimumNumber Float.nan 1.0 = 1.0
#test Float.minimumNumber 1.0 Float.nan = 1.0
#test (Float.minimumNumber Float.nan Float.nan).isNaN
#test Float.minimumNumber Float.nan (-Float.inf) = -Float.inf
#test Float.minimumNumber Float.nan Float.inf = Float.inf
#test Float.minimumNumber Float.inf Float.nan = Float.inf
-- The sign of a zero survives the `NaN` being dropped.
#test Float.minimumNumber Float.nan (-0.0) = -0.0
#test Float.minimumNumber (-0.0) Float.nan = -0.0
#test Float.minimumNumber Float.nan 0.0 = 0.0
#test Float.minimumNumber (0.0 / 0.0) 1.0 = 1.0

#test Float.maximumNumber Float.nan 1.0 = 1.0
#test Float.maximumNumber 1.0 Float.nan = 1.0
#test (Float.maximumNumber Float.nan Float.nan).isNaN
#test Float.maximumNumber Float.nan (-Float.inf) = -Float.inf
#test Float.maximumNumber Float.nan Float.inf = Float.inf
#test Float.maximumNumber (-Float.inf) Float.nan = -Float.inf
#test Float.maximumNumber Float.nan (-0.0) = -0.0
#test Float.maximumNumber (-0.0) Float.nan = -0.0
#test Float.maximumNumber Float.nan 0.0 = 0.0
#test Float.maximumNumber (0.0 / 0.0) 1.0 = 1.0

/-! ### Exhaustive sweep over a sorted list of non-`NaN` values -/

/-- Test values in ascending order, with `-0.0` before `0.0` as the operations order them. -/
def sorted : List Float :=
  [-Float.inf, -maxFinite, -1.0, -minSubnormal, -0.0, 0.0,
    minSubnormal, 1.0, maxFinite, Float.inf]

-- For `a ≤ b` in list order the minimum is `a` and the maximum is `b` bit-for-bit, in either
-- argument order.
#test (pairsLe sorted).all fun (a, b) => Float.minimum a b = a && Float.minimum b a = a
#test (pairsLe sorted).all fun (a, b) => Float.maximum a b = b && Float.maximum b a = b
#test (pairsLe sorted).all fun (a, b) =>
  Float.minimumNumber a b = a && Float.minimumNumber b a = a
#test (pairsLe sorted).all fun (a, b) =>
  Float.maximumNumber a b = b && Float.maximumNumber b a = b

-- `NaN` in either position: propagated by `minimum` and `maximum`, dropped by the `Number`
-- variants.
#test sorted.all fun a =>
  (Float.minimum Float.nan a).isNaN && (Float.minimum a Float.nan).isNaN
#test sorted.all fun a =>
  (Float.maximum Float.nan a).isNaN && (Float.maximum a Float.nan).isNaN
#test sorted.all fun a =>
  Float.minimumNumber Float.nan a = a && Float.minimumNumber a Float.nan = a
#test sorted.all fun a =>
  Float.maximumNumber Float.nan a = a && Float.maximumNumber a Float.nan = a

/-! ## `Float32` -/

-- Sanity check for the technique: `=` tells the two zeros apart.
#test ¬ ((0.0 : Float32) = -0.0)

/-- The smallest positive subnormal `Float32`. -/
def minSubnormal32 : Float32 := Float32.ofBits 1
/-- The largest finite `Float32`. -/
def maxFinite32 : Float32 := Float32.ofBits 0x7F7FFFFF

/-! ### Ordered operands -/

#test Float32.minimum 1.0 2.0 = 1.0
#test Float32.minimum 2.0 1.0 = 1.0
#test Float32.minimum (-1.0) 1.0 = -1.0
#test Float32.minimum 3.0 3.0 = 3.0
#test Float32.minimum minSubnormal32 0.0 = 0.0
#test Float32.minimum (-minSubnormal32) 0.0 = -minSubnormal32
#test Float32.minimum maxFinite32 Float32.inf = maxFinite32
#test Float32.minimum (-Float32.inf) (-maxFinite32) = -Float32.inf

#test Float32.maximum 1.0 2.0 = 2.0
#test Float32.maximum 2.0 1.0 = 2.0
#test Float32.maximum (-1.0) 1.0 = 1.0
#test Float32.maximum 3.0 3.0 = 3.0
#test Float32.maximum minSubnormal32 0.0 = minSubnormal32
#test Float32.maximum (-minSubnormal32) 0.0 = 0.0
#test Float32.maximum maxFinite32 Float32.inf = Float32.inf
#test Float32.maximum (-Float32.inf) (-maxFinite32) = -maxFinite32

#test Float32.minimumNumber 1.0 2.0 = 1.0
#test Float32.minimumNumber 2.0 1.0 = 1.0
#test Float32.minimumNumber (-1.0) 1.0 = -1.0
#test Float32.minimumNumber 3.0 3.0 = 3.0
#test Float32.minimumNumber minSubnormal32 0.0 = 0.0
#test Float32.minimumNumber (-minSubnormal32) 0.0 = -minSubnormal32
#test Float32.minimumNumber maxFinite32 Float32.inf = maxFinite32
#test Float32.minimumNumber (-Float32.inf) (-maxFinite32) = -Float32.inf

#test Float32.maximumNumber 1.0 2.0 = 2.0
#test Float32.maximumNumber 2.0 1.0 = 2.0
#test Float32.maximumNumber (-1.0) 1.0 = 1.0
#test Float32.maximumNumber 3.0 3.0 = 3.0
#test Float32.maximumNumber minSubnormal32 0.0 = minSubnormal32
#test Float32.maximumNumber (-minSubnormal32) 0.0 = 0.0
#test Float32.maximumNumber maxFinite32 Float32.inf = Float32.inf
#test Float32.maximumNumber (-Float32.inf) (-maxFinite32) = -maxFinite32

/-! ### Signed zeros: `-0.0 < 0.0` -/

#test Float32.minimum 0.0 (-0.0) = -0.0
#test Float32.minimum (-0.0) 0.0 = -0.0
#test Float32.minimum 0.0 0.0 = 0.0
#test Float32.minimum (-0.0) (-0.0) = -0.0

#test Float32.maximum 0.0 (-0.0) = 0.0
#test Float32.maximum (-0.0) 0.0 = 0.0
#test Float32.maximum 0.0 0.0 = 0.0
#test Float32.maximum (-0.0) (-0.0) = -0.0

#test Float32.minimumNumber 0.0 (-0.0) = -0.0
#test Float32.minimumNumber (-0.0) 0.0 = -0.0
#test Float32.minimumNumber 0.0 0.0 = 0.0
#test Float32.minimumNumber (-0.0) (-0.0) = -0.0

#test Float32.maximumNumber 0.0 (-0.0) = 0.0
#test Float32.maximumNumber (-0.0) 0.0 = 0.0
#test Float32.maximumNumber 0.0 0.0 = 0.0
#test Float32.maximumNumber (-0.0) (-0.0) = -0.0

/-! ### Infinities -/

#test Float32.minimum (-Float32.inf) 1.0 = -Float32.inf
#test Float32.minimum 1.0 (-Float32.inf) = -Float32.inf
#test Float32.minimum Float32.inf 1.0 = 1.0
#test Float32.minimum Float32.inf (-Float32.inf) = -Float32.inf
#test Float32.minimum Float32.inf Float32.inf = Float32.inf

#test Float32.maximum (-Float32.inf) 1.0 = 1.0
#test Float32.maximum 1.0 (-Float32.inf) = 1.0
#test Float32.maximum Float32.inf 1.0 = Float32.inf
#test Float32.maximum Float32.inf (-Float32.inf) = Float32.inf
#test Float32.maximum Float32.inf Float32.inf = Float32.inf

#test Float32.minimumNumber (-Float32.inf) 1.0 = -Float32.inf
#test Float32.minimumNumber 1.0 (-Float32.inf) = -Float32.inf
#test Float32.minimumNumber Float32.inf 1.0 = 1.0
#test Float32.minimumNumber Float32.inf (-Float32.inf) = -Float32.inf
#test Float32.minimumNumber Float32.inf Float32.inf = Float32.inf

#test Float32.maximumNumber (-Float32.inf) 1.0 = 1.0
#test Float32.maximumNumber 1.0 (-Float32.inf) = 1.0
#test Float32.maximumNumber Float32.inf 1.0 = Float32.inf
#test Float32.maximumNumber Float32.inf (-Float32.inf) = Float32.inf
#test Float32.maximumNumber Float32.inf Float32.inf = Float32.inf

/-! ### `NaN`: `minimum` and `maximum` propagate it, the `Number` variants prefer the number -/

#test (Float32.minimum Float32.nan 1.0).isNaN
#test (Float32.minimum 1.0 Float32.nan).isNaN
#test (Float32.minimum Float32.nan Float32.nan).isNaN
#test (Float32.minimum Float32.nan (-Float32.inf)).isNaN
#test (Float32.minimum (-Float32.inf) Float32.nan).isNaN
#test (Float32.minimum Float32.nan (-0.0)).isNaN
-- A `NaN` produced by arithmetic (typically with the sign bit set) behaves the same.
#test (Float32.minimum (0.0 / 0.0) 1.0).isNaN

#test (Float32.maximum Float32.nan 1.0).isNaN
#test (Float32.maximum 1.0 Float32.nan).isNaN
#test (Float32.maximum Float32.nan Float32.nan).isNaN
#test (Float32.maximum Float32.nan Float32.inf).isNaN
#test (Float32.maximum Float32.inf Float32.nan).isNaN
#test (Float32.maximum Float32.nan 0.0).isNaN
#test (Float32.maximum (0.0 / 0.0) 1.0).isNaN

#test Float32.minimumNumber Float32.nan 1.0 = 1.0
#test Float32.minimumNumber 1.0 Float32.nan = 1.0
#test (Float32.minimumNumber Float32.nan Float32.nan).isNaN
#test Float32.minimumNumber Float32.nan (-Float32.inf) = -Float32.inf
#test Float32.minimumNumber Float32.nan Float32.inf = Float32.inf
#test Float32.minimumNumber Float32.inf Float32.nan = Float32.inf
-- The sign of a zero survives the `NaN` being dropped.
#test Float32.minimumNumber Float32.nan (-0.0) = -0.0
#test Float32.minimumNumber (-0.0) Float32.nan = -0.0
#test Float32.minimumNumber Float32.nan 0.0 = 0.0
#test Float32.minimumNumber (0.0 / 0.0) 1.0 = 1.0

#test Float32.maximumNumber Float32.nan 1.0 = 1.0
#test Float32.maximumNumber 1.0 Float32.nan = 1.0
#test (Float32.maximumNumber Float32.nan Float32.nan).isNaN
#test Float32.maximumNumber Float32.nan (-Float32.inf) = -Float32.inf
#test Float32.maximumNumber Float32.nan Float32.inf = Float32.inf
#test Float32.maximumNumber (-Float32.inf) Float32.nan = -Float32.inf
#test Float32.maximumNumber Float32.nan (-0.0) = -0.0
#test Float32.maximumNumber (-0.0) Float32.nan = -0.0
#test Float32.maximumNumber Float32.nan 0.0 = 0.0
#test Float32.maximumNumber (0.0 / 0.0) 1.0 = 1.0

/-! ### Exhaustive sweep over a sorted list of non-`NaN` values -/

/-- Test values in ascending order, with `-0.0` before `0.0` as the operations order them. -/
def sorted32 : List Float32 :=
  [-Float32.inf, -maxFinite32, -1.0, -minSubnormal32, -0.0, 0.0,
    minSubnormal32, 1.0, maxFinite32, Float32.inf]

-- For `a ≤ b` in list order the minimum is `a` and the maximum is `b` bit-for-bit, in either
-- argument order.
#test (pairsLe sorted32).all fun (a, b) => Float32.minimum a b = a && Float32.minimum b a = a
#test (pairsLe sorted32).all fun (a, b) => Float32.maximum a b = b && Float32.maximum b a = b
#test (pairsLe sorted32).all fun (a, b) =>
  Float32.minimumNumber a b = a && Float32.minimumNumber b a = a
#test (pairsLe sorted32).all fun (a, b) =>
  Float32.maximumNumber a b = b && Float32.maximumNumber b a = b

-- `NaN` in either position: propagated by `minimum` and `maximum`, dropped by the `Number`
-- variants.
#test sorted32.all fun a =>
  (Float32.minimum Float32.nan a).isNaN && (Float32.minimum a Float32.nan).isNaN
#test sorted32.all fun a =>
  (Float32.maximum Float32.nan a).isNaN && (Float32.maximum a Float32.nan).isNaN
#test sorted32.all fun a =>
  Float32.minimumNumber Float32.nan a = a && Float32.minimumNumber a Float32.nan = a
#test sorted32.all fun a =>
  Float32.maximumNumber Float32.nan a = a && Float32.maximumNumber a Float32.nan = a
