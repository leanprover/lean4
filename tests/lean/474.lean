import Lean
open Lean Meta

#eval show MetaM Unit from do
  let e ← withLetDecl `y (mkConst ``Nat) (mkConst ``Nat.zero) fun y => do
    let m ← mkFreshExprMVar (mkConst ``Nat)
    assignExprMVar m.mvarId! y
    let e ← mkApp2 (mkConst ``Nat.add) m y
    -- goal: construct λ y, e
    dbg_trace (← ppExpr (← mkLambdaFVars #[y] e)) -- doesn't work: creates let
    dbg_trace (← ppExpr (← instantiateMVars <| -- doesn't work: contains free variable
      mkLambda `y BinderInfo.default (mkConst ``Nat) (e.abstract #[y])))
    instantiateMVars <| -- doesn't work: contains free variable
      mkLambda `y BinderInfo.default (mkConst ``Nat) (e.abstract #[y])
  dbg_trace (← ppExpr e)

#eval show MetaM Unit from
  withLetDecl `y (mkConst ``Nat) (mkConst ``Nat.zero) fun y => do
    let m ← mkFreshExprMVar (mkConst ``Nat)
    assignExprMVar m.mvarId! y
    let e ← mkApp2 (mkConst ``Nat.add) m y
    -- goal: construct λ y, e
     dbg_trace (← instantiateMVars <| -- doesn't work: contains free variable
      mkLambda `y BinderInfo.default (mkConst ``Nat) (← abstract e #[y]))

#eval show MetaM Unit from do
  let (e, m) ← withLetDecl `y (mkConst ``Nat) (mkConst ``Nat.zero) fun y => do
    let m ← mkFreshExprMVar (mkConst ``Nat) (kind := MetavarKind.syntheticOpaque)
    let e ← mkApp2 (mkConst ``Nat.add) m y
    dbg_trace (← ppExpr e)
    dbg_trace (← ppExpr (← abstract e #[y]))
    let e ← instantiateMVars <| -- doesn't work: contains free variable
      mkLambda `y BinderInfo.default (mkConst ``Nat) (← abstract e #[y])
    assignExprMVar m.mvarId! (mkApp2 (mkConst ``Nat.add) y y)
    return (e, m)
  dbg_trace (← ppExpr (← instantiateMVars e))
