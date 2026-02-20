import Lean
set_option warn.sorry false

def f [Add α] (a : α) := a + a
abbrev id' (a : α) := a
abbrev addNat : Add Nat := ⟨Nat.add⟩

set_option pp.explicit true

/--
trace: a b : Nat
⊢ @Eq Nat (@f Nat (@id' (Add Nat) addNat) a) b
---
trace: a b : Nat
⊢ @Eq Nat (@f Nat addNat a) b
-/
#guard_msgs in
example : @f _ (id' addNat) a = id b := by
  dsimp [id']
  trace_state -- `id'` was not unfolded because it is part of an instance
  dsimp +instances [id']
  trace_state
  sorry

/--
trace: a b : Nat
⊢ @Eq Nat (@f Nat addNat a) b
-/
#guard_msgs in
set_option backward.dsimp.instances true in
example : @f _ (id' addNat) a = id b := by
  dsimp [id']
  trace_state
  sorry

set_option linter.unusedSimpArgs false

/--
trace: a b : Nat
⊢ @Eq Nat (@f Nat (@id' (Add Nat) addNat) a) b
---
trace: a b : Nat
⊢ @Eq Nat (@f Nat addNat a) b
-/
#guard_msgs in
example : @f _ (id' addNat) a = id b := by
  simp [id']
  trace_state -- `id'` was not unfolded because it is part of an instance
  simp +instances [id']
  trace_state
  sorry

/--
trace: a b : Nat
⊢ @Eq Nat (@f Nat addNat a) b
-/
#guard_msgs in
set_option backward.dsimp.instances true in
example : @f _ (id' addNat) a = id b := by
  simp [id']
  trace_state
  sorry
