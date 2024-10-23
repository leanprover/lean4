import Lean
open Lean Meta

open PrettyPrinter Delaborator SubExpr in
@[delab fvar]
def delabFVar : Delab := do
  let Expr.fvar fvarId ← getExpr | unreachable!
  let none := (← getLCtx).find? fvarId | failure
  return mkIdent `FREE

#eval do
  let e ← withLetDecl `y (mkConst ``Nat) (mkConst ``Nat.zero) fun y => do
    let m ← mkFreshExprMVar (mkConst ``Nat)
    m.mvarId!.assign y
    let e := mkApp2 (mkConst ``Nat.add) m y
    -- goal: construct λ y, e
    dbg_trace (← ppExpr (← mkLambdaFVars #[y] e)) -- doesn't work: creates let
    dbg_trace (← ppExpr (← instantiateMVars <| -- doesn't work: contains free variable
      mkLambda `y BinderInfo.default (mkConst ``Nat) (e.abstract #[y])))
    instantiateMVars <| -- doesn't work: contains free variable
      mkLambda `y BinderInfo.default (mkConst ``Nat) (e.abstract #[y])
  dbg_trace (← ppExpr e)

#eval
  withLetDecl `y (mkConst ``Nat) (mkConst ``Nat.zero) fun y => do
    let m ← mkFreshExprMVar (mkConst ``Nat)
    m.mvarId!.assign y
    let e := mkApp2 (mkConst ``Nat.add) m y
    -- goal: construct λ y, e
     dbg_trace (← instantiateMVars <| -- doesn't work: contains free variable
      mkLambda `y BinderInfo.default (mkConst ``Nat) (← e.abstractM #[y]))

#eval do
  let (e, _) ← withLetDecl `y (mkConst ``Nat) (mkConst ``Nat.zero) fun y => do
    let m ← mkFreshExprMVar (mkConst ``Nat) (kind := MetavarKind.syntheticOpaque)
    let e := mkApp2 (mkConst ``Nat.add) m y
    dbg_trace (← ppExpr e)
    dbg_trace (← ppExpr (← e.abstractM #[y]))
    let e ← instantiateMVars <| -- doesn't work: contains free variable
      mkLambda `y BinderInfo.default (mkConst ``Nat) (← e.abstractM #[y])
    m.mvarId!.assign (mkApp2 (mkConst ``Nat.add) y y)
    return (e, m)
  dbg_trace (← ppExpr (← instantiateMVars e))
