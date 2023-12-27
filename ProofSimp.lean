import Lean.Meta.Tactic.Simp
import Lean

open Lean Elab Meta Tactic

@[simp]
theorem un_of_eq_true (α : Type _) (a b : α) (h : a = b) :
    of_eq_true (Eq.trans (congrFun (congrArg Eq h) b) (eq_self b)) = h := rfl

elab (name := test) "test " t:tacticSeq : tactic => withMainContext do
  let g ← getMainGoal
  evalTactic t
  let expr ← instantiateMVars (mkMVar g)

  -- let s : SimpTheorems ← getSimpTheorems
  let s : SimpTheorems := default
  let s ← s.addConst ``un_of_eq_true
  let ctxt := { config := {simpProofs := true}, simpTheorems := #[s], congrTheorems := default } -- (← getSimpCongrTheorems) }
  let (r, _) ← Lean.Meta.simp expr ctxt
  logInfo $ m!"Before simplifying:\n{expr}\n" ++
            m!"After simplifying:\n{r.expr}"

-- set_option pp.rawOnError true
set_option trace.Meta.Tactic.simp true
-- set_option trace.Meta.Tactic.simp.heads true
set_option trace.Meta.Tactic.simp.rewrite true
-- set_option trace.Debug.Meta.Tactic.simp true
set_option trace.Meta.isDefEq true
set_option trace.Meta.isDefEq.assign true

example x : 0 + (0 + x) = x := by
    -- show_term simp
    test (
        exact of_eq_true
         (Eq.trans (congrFun (congrArg Eq (Eq.trans (congrArg (HAdd.hAdd 0) (Nat.zero_add x)) (Nat.zero_add x))) x)
          (eq_self x)))
