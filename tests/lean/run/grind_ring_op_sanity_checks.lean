open Lean Grind

/--
error: error while initializing `grind ring` operators:
instance for `HAdd.hAdd` ⏎
  instHAdd
is not definitionally equal to the expected one ⏎
  instHAdd
when only reducible definitions and instances are reduced
-/
#guard_msgs in
example [CommRing α] [Add α] (a b : α) : a = OfNat.ofNat (α := α) 5 → b = 5 → a + b = 10 := by
  grind

/--
error: error while initializing `grind ring` operators:
instance for `HMul.hMul` ⏎
  instHMul
is not definitionally equal to the expected one ⏎
  instHMul
when only reducible definitions and instances are reduced
-/
#guard_msgs in
example [CommRing α] [Mul α] (a b : α) : a = OfNat.ofNat (α := α) 5 → b = 5 → a * b = 25 := by
  grind

/--
error: error while initializing `grind ring` operators:
instance for `HSub.hSub` ⏎
  instHSub
is not definitionally equal to the expected one ⏎
  instHSub
when only reducible definitions and instances are reduced
-/
#guard_msgs in
example [CommRing α] [Sub α] (a b : α) : a = OfNat.ofNat (α := α) 5 → b = 5 → a - b = 0 := by
  set_option trace.grind.issues true in
  grind

/--
error: error while initializing `grind ring` operators:
instance for `HPow.hPow` ⏎
  inst_1
is not definitionally equal to the expected one ⏎
  Semiring.npow
when only reducible definitions and instances are reduced
-/
#guard_msgs in
example [CommRing α] [HPow α Nat α] (a b : α) : a = OfNat.ofNat (α := α) 5 → a^2 = 25 := by
  grind

/--
error: error while initializing `grind ring` operators:
instance for `Neg.neg` ⏎
  inst_1
is not definitionally equal to the expected one ⏎
  inst.toNeg
when only reducible definitions and instances are reduced
-/
#guard_msgs in
example [CommRing α] [Neg α] (a : α) : a = 5 → -a = -5 := by
  grind

/--
error: error while initializing `grind ring` operators:
instance for `Inv.inv` ⏎
  inst_1
is not definitionally equal to the expected one ⏎
  inst.toInv
when only reducible definitions and instances are reduced
-/
#guard_msgs in
example [Field α] [Inv α] (a : α) : a = 5 → -a = -5 := by
  grind
