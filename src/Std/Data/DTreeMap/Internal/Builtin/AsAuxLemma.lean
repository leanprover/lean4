prelude
import Std.Data.DTreeMap.Internal.AsAuxLemma
import Lean.Elab.Tactic

open Lean Meta Elab Tactic

namespace Std.Internal.TreeMap

@[builtin_tactic as_aux_lemma]
def elabAsAuxLemma : Tactic
| `(tactic| as_aux_lemma => $s) =>
  liftMetaTactic fun mvarId => do
    let (mvars, _) ← runTactic mvarId s
    unless mvars.isEmpty do
      throwError "Left-over goals, cannot abstract"
    let e ← instantiateMVars (mkMVar mvarId)
    let e ← mkAuxTheorem (`Std.DTreeMap.Internal.Impl ++ (← mkFreshUserName `test)) (← mvarId.getType) e
    mvarId.assign e
    return []
| _ => throwError "Invalid as_aux_lemma syntax"
