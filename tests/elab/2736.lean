set_option autoImplicit true

section Mathlib.Algebra.Group.Defs

class MulOneClass (M : Type) extends One M, Mul M where
  one_mul : ∀ a : M, 1 * a = a

export MulOneClass (one_mul)

end Mathlib.Algebra.Group.Defs

section Mathlib.Algebra.Ring.Defs

class Distrib (R : Type) extends Mul R, Add R where
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

class RightDistribClass (R : Type) [Mul R] [Add R] : Prop where
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

instance Distrib.rightDistribClass (R : Type) [Distrib R] : RightDistribClass R :=
  ⟨Distrib.right_distrib⟩

theorem add_mul [Mul R] [Add R] [RightDistribClass R] (a b c : R) :
    (a + b) * c = a * c + b * c :=
  RightDistribClass.right_distrib a b c

theorem add_one_mul [Add α] [MulOneClass α] [RightDistribClass α] (a b : α) :
    (a + 1) * b = a * b + b := by
  rw [add_mul, one_mul]

class Semiring (R : Type) extends Distrib R, MulOneClass R

end Mathlib.Algebra.Ring.Defs

section Mathlib.Data.Nat.Basic

instance : Semiring Nat where
  add := Nat.add
  mul := Nat.mul
  one := Nat.succ Nat.zero
  one_mul := sorry
  right_distrib := sorry

end Mathlib.Data.Nat.Basic

#synth MulOneClass Nat       -- works
#synth RightDistribClass Nat -- works

theorem ex1 [Add α] [MulOneClass α] [RightDistribClass α] (a b : α) :
    (a + 1) * b = a * b + b := by
  sorry

#check (ex1) -- should work
#check (add_one_mul) -- should work
#check @add_one_mul

example {a b : Nat} : (a + 1) * b = a * b + b := by
  have := add_one_mul a b -- works
  rw [add_one_mul] -- should work

example {a b : Nat} : (a + 1) * b = a * b + b := by
  rw [add_one_mul] -- should work
