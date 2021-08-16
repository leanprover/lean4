import Lean

axiom ex (p q : Prop) (h : p ∧ q) : q ∧ q

open Lean in
open Lean.Meta in
def test : MetaM Unit := do
  let type := (← getConstInfo ``ex).type
  let mvar ← mkFreshExprMVar type
  let (#[p, q, h], mvarId) ← introNP mvar.mvarId! 3 | throwError "unexpected"
  trace[Meta.debug] "{MessageData.ofGoal mvarId}"
  let (s₁, s₂) ← byCases mvarId (mkFVar p) `hAux
  trace[Meta.debug] "{MessageData.ofGoal s₁.mvarId}\n------\n{MessageData.ofGoal s₂.mvarId}"
  return ()

set_option trace.Meta.debug true
#eval test
