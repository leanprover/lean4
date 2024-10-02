/-!
This test should catch intentional or accidental changes to how projections are rewritten by
various tactics
-/

structure S where
  proj : Nat

variable (P : Nat → Prop)

section structure_abstract

variable (s : S)

/--
error: tactic 'fail' failed
P : Nat → Prop
s : S
⊢ P s.1
-/
#guard_msgs in
example : P (s.proj) := by
  rw [S.proj]
  -- Cannot use
  -- guard_target =ₛ P s.1
  -- here as, as that elaborates as `P s.proj`
  fail

/--
error: tactic 'fail' failed
P : Nat → Prop
s : S
⊢ P s.1
-/
#guard_msgs in
example : P (s.proj) := by
  unfold S.proj
  fail

/-- error: simp made no progress -/
#guard_msgs in
example : P (s.proj) := by
  simp [S.proj]
  fail

end structure_abstract

section structure_concrete

variable (n : Nat)
/--
error: tactic 'fail' failed
P : Nat → Prop
n : Nat
⊢ P { proj := n }.1
-/
#guard_msgs in
example : P (S.proj ⟨n⟩) := by rw [S.proj]; fail
  -- Cannot use
  -- guard_target =ₛ P s.1
  -- here as, as that elaborates as `P s.proj`

/--
error: tactic 'fail' failed
P : Nat → Prop
n : Nat
⊢ P { proj := n }.1
-/
#guard_msgs in
example : P (S.proj ⟨n⟩) := by unfold S.proj; fail

/--
error: tactic 'fail' failed
P : Nat → Prop
n : Nat
⊢ P n
-/
#guard_msgs in
example : P (S.proj ⟨n⟩) := by simp [S.proj]; fail -- NB: reduces the projectino

end structure_concrete

class C (α : Type) where
  meth : Nat

section class_abstract

instance : C Bool where
  meth := 42

variable (α : Type) [C α]

/--
error: tactic 'fail' failed
P : Nat → Prop
α : Type
inst✝ : C α
⊢ P inst✝.1
-/
#guard_msgs in
example : P (C.meth α) := by rw [C.meth]; fail

/--
error: tactic 'fail' failed
P : Nat → Prop
α : Type
inst✝ : C α
⊢ P inst✝.1
-/
#guard_msgs in
example : P (C.meth α) := by unfold C.meth; fail

/-- error: simp made no progress -/
#guard_msgs in
example : P (C.meth α) := by simp [C.meth]; fail

end class_abstract

section class_concrete

/--
error: tactic 'fail' failed
P : Nat → Prop
⊢ P instCBool.1
-/
#guard_msgs in
example : P (C.meth Bool) := by rw [C.meth]; fail

/--
error: tactic 'fail' failed
P : Nat → Prop
⊢ P instCBool.1
-/
#guard_msgs in
example : P (C.meth Bool) := by unfold C.meth; fail

/--
error: tactic 'fail' failed
P : Nat → Prop
⊢ P 42
-/
#guard_msgs in
example : P (C.meth Bool) := by simp [C.meth]; fail -- NB: Unfolds the instance `instCBool`!


end class_concrete
