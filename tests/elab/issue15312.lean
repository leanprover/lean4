import Lean

/-!
Regression test for #15312: the unfold theorems of a mutual `partial_fixpoint` block are proved
from the block's fixpoint equation `_fix_eq`, so that their proofs do not contain the functional
and the monotonicity proof of the whole block.
-/

open Lean Meta in
/-- Checks that the unfold theorem of `declName` is proved via `_fix_eq`. -/
def checkUnfoldViaFixEq (declName : Name) : MetaM Unit := do
  let some eqDef ← getUnfoldEqnFor? declName | throwError "no unfold theorem for {declName}"
  let consts := (← getConstInfo eqDef).value! (allowOpaque := true) |>.getUsedConstants
  let usesFixEq := consts.any fun | .str _ "_fix_eq" => true | _ => false
  unless usesFixEq && !consts.contains ``Lean.Order.fix_eq &&
      !consts.contains ``Lean.Order.lfp_monotone_fix do
    throwError "unexpected constants in the proof of {eqDef}: {consts}"

namespace Ring

mutual
def f0 (n : Nat) : Option Nat :=
  match n with
  | 0 => pure 0
  | m+1 => do
    let a ← f1 m
    pure (a + 1)
partial_fixpoint
def f1 (n : Nat) : Option Nat :=
  match n with
  | 0 => pure 0
  | m+1 => do
    let a ← f2 m
    pure (a + 1)
partial_fixpoint
def f2 (n : Nat) : Option Nat :=
  match n with
  | 0 => pure 0
  | m+1 => do
    let a ← f0 m
    pure (a + 1)
partial_fixpoint
end

/--
info: Ring.f1.eq_def (n : Nat) :
  f1 n =
    match n with
    | 0 => pure 0
    | m.succ => do
      let a ← f2 m
      pure (a + 1)
-/
#guard_msgs in #check f1.eq_def

/--
info: equations:
theorem Ring.f2.eq_1 : f2 0 = pure 0
theorem Ring.f2.eq_2 : ∀ (m : Nat),
  f2 m.succ = do
    let a ← f0 m
    pure (a + 1)
-/
#guard_msgs in #print equations f2

#eval checkUnfoldViaFixEq ``f0
#eval checkUnfoldViaFixEq ``f1
#eval checkUnfoldViaFixEq ``f2

example : f1 1 = some 1 := by rw [f1, f2]; rfl
example : f2 1 = some 1 := by unfold f2 f0; rfl
example : f0 2 = some 2 := by simp only [f0, f1, f2]; rfl

end Ring

namespace FixedParams

-- The fixed parameters are in different positions, so they are not a common prefix
mutual
def g (b : Bool) (n : Nat) : Option Nat :=
  match n with
  | 0 => pure 0
  | m+1 => do
    let a ← h m b
    pure (if b then a + 1 else a)
partial_fixpoint
def h (n : Nat) (b : Bool) : Option Nat :=
  match n with
  | 0 => pure 1
  | m+1 => g b m
partial_fixpoint
end

#eval checkUnfoldViaFixEq ``g
#eval checkUnfoldViaFixEq ``h

/--
info: equations:
theorem FixedParams.h.eq_1 : ∀ (b : Bool), h 0 b = pure 1
theorem FixedParams.h.eq_2 : ∀ (b : Bool) (m : Nat), h m.succ b = g b m
-/
#guard_msgs in #print equations h

example : g true 1 = some 2 := by rw [g, h]; rfl

end FixedParams

namespace Univ

mutual
def p {α : Type u} (x : α) (n : Nat) : Option (List α) :=
  match n with
  | 0 => pure []
  | m+1 => do
    let l ← q x m
    pure (x :: l)
partial_fixpoint
def q {α : Type u} (x : α) (n : Nat) : Option (List α) :=
  match n with
  | 0 => pure [x]
  | m+1 => p x m
partial_fixpoint
end

#eval checkUnfoldViaFixEq ``p
#eval checkUnfoldViaFixEq ``q

example : p 'a' 2 = some ['a'] := by rw [p, q, p]; rfl

end Univ

namespace Pred

mutual
def Even (n : Nat) : Prop :=
  n = 0 ∨ ∃ m, n = m + 1 ∧ Odd m
inductive_fixpoint
def Odd (n : Nat) : Prop :=
  ∃ m, n = m + 1 ∧ Even m
inductive_fixpoint
end

#eval checkUnfoldViaFixEq ``Even
#eval checkUnfoldViaFixEq ``Odd

example : Odd 1 := by
  rw [Odd]
  exact ⟨0, rfl, by rw [Even]; exact .inl rfl⟩

end Pred
