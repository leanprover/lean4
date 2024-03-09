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
    let some { mvarIdPending .. } ← getDelayedMVarAssignment? m'.mvarId!
      | IO.println f!"m' is not delayed-assigned"
    IO.println (mvarIdPending == m.mvarId!)
    IO.println (← mvarIdPending.isDelayedAssigned)
    IO.println (← getExprMVarAssignment? m'.mvarId!)
    assert! (← withAssignableSyntheticOpaque <| isDefEq b (mkNatLit 0))
    IO.println (← getExprMVarAssignment? m'.mvarId!)
    IO.println (← getExprMVarAssignment? m.mvarId!)
    IO.println (← ppExpr (← instantiateMVars m'))
    IO.println (← ppExpr (← instantiateMVars b))
    IO.println (← ppExpr m)
    return ()

#eval tst
