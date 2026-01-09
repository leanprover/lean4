import Lean

open Lean Meta

def tst : MetaM Unit := do
  let (e, m) ← withLocalDeclD `x (mkConst ``Nat) fun x => do
    let m ← mkFreshExprMVar (mkConst ``Nat) .syntheticOpaque
    return (← mkLambdaFVars #[x] m, m)
  IO.println (← ppExpr e)
  lambdaTelescope e fun _ b => do
    let m' := b.getAppFn
    assert! m'.isMVar
    assert! (← withAssignableSyntheticOpaque <| isDefEq b (mkNatLit 0))
    IO.println (← getExprMVarAssignment? m'.mvarId!)
    let some m ← getExprMVarAssignment? m.mvarId!
      | IO.println f!"{m} is not assigned"
    -- Currently, `m` gets assigned to an intermediate mvar to clear local hypotheses.
    -- See `expandDelayedAssigned?` in Lean.Meta.ExprDefEq.
    assert! m.isMVar
    IO.println (← getExprMVarAssignment? m.mvarId!)
    IO.println (← ppExpr (← instantiateMVars b))
    IO.println (← ppExpr m)
    return ()

#eval tst
