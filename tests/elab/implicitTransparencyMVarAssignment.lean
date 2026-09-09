/-!
# Reproduction: Transparency-Related Metavariable Assignment Failure

In `iSupLift` from `Mathlib.Algebra.Algebra.NonUnitalSubalgebra`, we observed a failue assigning a
metavariable that appeared when we made `Set.Mem` implicit-reducible but vanished again when we made
`Membership.mem` implicit-reducible, too.
-/

def MySet := Nat → Prop
def MyMem (s : MySet) (a : Nat) : Prop := s a
instance instMemSet : Membership Nat MySet := ⟨MyMem⟩

class MySetLike (β : Type) where
  coe : β → MySet
instance instMemLike {β} [MySetLike β] : Membership Nat β := ⟨fun p a => a ∈ MySetLike.coe p⟩

structure MySub where carrier : MySet
instance instMySetLikeMySub : MySetLike MySub := ⟨MySub.carrier⟩

def cMySub : MySub := ⟨fun _ => True⟩
def aAtom : Nat := 0

/-- A function whose type argument is implicit. -/
def wrap {τ : Type} (_ : τ) : Nat := 0

@[simp] theorem wrap_mk {β : Type} [MySetLike β] (s : β) (a : Nat) (h : a ∈ s) :
    wrap (⟨a, h⟩ : {y // y ∈ s}) = 0 := rfl

set_option allowUnsafeReducibility true

section A

/-! `MyMem` semireducible  -/

#guard_msgs in
example (h : aAtom ∈ (MySetLike.coe cMySub : MySet)) :
    wrap (⟨aAtom, h⟩ : {y // y ∈ (MySetLike.coe cMySub : MySet)}) = 0 := by
  simp only [wrap_mk]

end A

section B

/-! `MyMem` implicit-reducible  -/

attribute [implicit_reducible] MyMem

#guard_msgs in
example (h : aAtom ∈ (MySetLike.coe cMySub : MySet)) :
    wrap (⟨aAtom, h⟩ : {y // y ∈ (MySetLike.coe cMySub : MySet)}) = 0 := by
  simp only [wrap_mk]

end B

section C

/-!
`MyMem` implicit-reducible, `Membership.mem` semireducible:
This failure reproduces the original issue in Mathlib, as observed in `iSupLift` from
`Mathlib.Algebra.Algebra.NonUnitalSubalgebra`.
-/

attribute [implicit_reducible] MyMem
attribute [semireducible] Membership.mem

/-- error: `simp` made no progress -/
#guard_msgs in
example (h : aAtom ∈ (MySetLike.coe cMySub : MySet)) :
    wrap (⟨aAtom, h⟩ : {y // y ∈ (MySetLike.coe cMySub : MySet)}) = 0 := by
  simp only [wrap_mk]

end C
