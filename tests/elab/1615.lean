import Lean.Elab.ElabRules
import Lean.Meta.Tactic.Replace

elab "test" h:ident : tactic => do
  let g ← Lean.Elab.Tactic.getMainGoal
  g.withContext do
    let ldec ← Lean.Meta.getLocalDeclFromUserName h.getId
    let f := ldec.fvarId
    let e ← Lean.Meta.whnf (← Lean.instantiateMVars ldec.type)
    let newgoal ← g.replaceLocalDeclDefEq f e
    Lean.Elab.Tactic.replaceMainGoal [newgoal]

def Nat.dvd (a b : Nat) := ∃ c, b = a * c

example (n : Nat) (h : Nat.dvd 2 n) : ∃ c, n = 2 * c := by
  test h
  with_reducible exact h
