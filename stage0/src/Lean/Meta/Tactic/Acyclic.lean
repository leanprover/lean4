/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.MatchUtil
import Lean.Meta.Tactic.Simp.Main

namespace Lean.MVarId
open Meta

private def isTarget (lhs rhs : Expr) : MetaM Bool := do
  if !lhs.isFVar || !lhs.occurs rhs then
    return false
  else
    return (← whnf rhs).isConstructorApp (← getEnv)

/--
  Close the given goal if `h` is a proof for an equality such as `as = a :: as`.
  Inductive datatypes in Lean are acyclic.
-/
def acyclic (mvarId : MVarId) (h : Expr) : MetaM Bool := mvarId.withContext do
  let type ← whnfD (← inferType h)
  trace[Meta.Tactic.acyclic] "type: {type}"
  let some (_, lhs, rhs) := type.eq? | return false
  if (← isTarget lhs rhs) then
    go h lhs rhs
  else if (← isTarget rhs lhs) then
    go (← mkEqSymm h) rhs lhs
  else
    return false
where
  go (h lhs rhs : Expr) : MetaM Bool := do
    try
      let sizeOf_lhs ← mkAppM ``sizeOf #[lhs]
      let sizeOf_rhs ← mkAppM ``sizeOf #[rhs]
      let sizeOfEq ← mkLT sizeOf_lhs sizeOf_rhs
      let hlt ← mkFreshExprSyntheticOpaqueMVar sizeOfEq
      -- TODO: we only need the `sizeOf` simp theorems
      match (← simpTarget hlt.mvarId! { config.arith := true, simpTheorems := #[ (← getSimpTheorems) ] }).1 with
      | some _ => return false
      | none   =>
        let heq ← mkCongrArg sizeOf_lhs.appFn! (← mkEqSymm h)
        let hlt_self ← mkAppM ``Nat.lt_of_lt_of_eq #[hlt, heq]
        let hlt_irrelf ← mkAppM ``Nat.lt_irrefl #[sizeOf_lhs]
        mvarId.assign (← mkFalseElim (← mvarId.getType) (mkApp hlt_irrelf hlt_self))
        trace[Meta.Tactic.acyclic] "succeeded"
        return true
    catch ex =>
      trace[Meta.Tactic.acyclic] "failed with\n{ex.toMessageData}"
      return false

builtin_initialize
  registerTraceClass `Meta.Tactic.acyclic

end Lean.MVarId
