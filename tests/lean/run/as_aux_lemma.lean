import Lean.Meta.Basic
import Lean.Util.NumObjs
import Lean.Elab.Tactic
import Init.Tactics

open Lean Meta Elab Tactic Parser.Tactic

elab_rules : tactic
| `(tactic| as_aux_lemma => $s) =>
  liftMetaTactic fun mvarId => do
    let (mvars, _) ← runTactic mvarId s
    unless mvars.isEmpty do
      throwError "Cannot abstract term into auxiliary lemma because there are open goals."
    let e ← instantiateMVars (mkMVar mvarId)
    let e ← mkAuxTheorem (`Lean.Elab.Tactic.AsAuxLemma ++ (← mkFreshUserName `auxLemma)) (← mvarId.getType) e
    mvarId.assign e
    return []

namespace Test

def thm : ∀ n : Nat, n = 0 + n := by as_aux_lemma =>
  intro n
  induction n
  · rfl
  · next ih =>
    rw [← Nat.succ_eq_add_one, Nat.add_succ, ← ih]

end Test

open Lean

def size (ns : Name) : MetaM Nat := do
  let env ← getEnv
  let mut totalSize : Nat := 0
  for (name, info) in env.constants do
    if ns.isPrefixOf name then
      if let some e := info.value? then
        let numObjs ← e.numObjs
        totalSize := totalSize + numObjs
  return totalSize

/--
info: theorem smaller than auxiliary lemma: true
-/
#guard_msgs in
run_meta do
  let thmSize ← size `Test
  let auxSize ← size `Lean.Elab.Tactic.AsAuxLemma
  logInfo m!"theorem smaller than auxiliary lemma: {decide $ thmSize < auxSize}"
