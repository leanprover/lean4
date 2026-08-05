/-!
Tests `simp +ground` on congruence for class constructors. The parent subobject
field is an instance argument with congruence kind `eq`, which used to panic with
`unknown constant _inhabitedExprDummy` (#12620).
-/

class A (α : Type) where
  a : α

class B (α : Type) extends A α where
  b : α
  hb : b = b

example (x y : Nat) (h : x = y) :
    (@B.mk Nat ⟨0⟩ x rfl) = (@B.mk Nat ⟨0⟩ y rfl) := by
  simp +ground [h]

opaque P : B Nat → Prop

example (x y : Nat) (h : x = y) (hyp : P (@B.mk Nat ⟨0⟩ x rfl)) :
    P (@B.mk Nat ⟨0⟩ y rfl) := by
  simp +ground [h] at hyp
  exact hyp
