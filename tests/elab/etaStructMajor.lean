import Lean
open Lean Meta Elab Tactic

set_option linter.defProp false

/-!
Structure eta on the major premise of a recursor, before or instead of reducing
the major to a constructor.
-/

/-- Closes an equality goal with `Eq.refl` of its right-hand side, unchecked. -/
macro "unchecked_rfl" : tactic => `(tactic|
  run_tac closeMainGoalUsing `unchecked fun goalType _ => do
    let some (_, _, rhs) := goalType.eq? | throwError "goal is not an equality"
    mkEqRefl rhs)

/-! A proof that has no weak head normal form (Coquand's paradox via `propext`). -/

theorem tautext {A B : Prop} (a : A) (b : B) : A = B := propext ⟨fun _ => b, fun _ => a⟩
def True' : Prop := ∀ A : Prop, A → A
def delta : True' → True' := fun z => z (True' → True') id z
def omega : True' := fun _ a => cast (tautext id a) delta
def Omega : True' := delta omega

/-! `Prod` major whose weak head normal form does not exist -/

def loopAcc : Acc (fun _ _ : Nat => False) 0 := Omega _ (Acc.intro 0 fun _ h => h.elim)
noncomputable def loopPair : Nat × Nat :=
  Acc.rec (motive := fun _ _ => Nat × Nat) (fun _ _ _ => (0, 0)) loopAcc
noncomputable def prodConst (p : Nat × Nat) : Nat := Prod.rec (motive := fun _ => Nat) (fun _ _ => 1) p

theorem prodMajorNoWhnf : prodConst loopPair = 1 := by unchecked_rfl
