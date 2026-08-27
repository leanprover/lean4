import Lean

open Lean Meta

def tst : MetaM Unit := do
  let (e, m) ← withLocalDeclD `x (mkConst ``Nat) fun x => do
    let m ← mkFreshExprMVar (mkConst ``Nat) .syntheticOpaque
    return (← mkLambdaFVars #[x] m, m)
  IO.println (← ppExpr e)
  lambdaTelescope e fun _ b => do
    assert! (← withAssignableSyntheticOpaque <| isDefEq b (mkNatLit 0))
    let m' := b.getAppFn
    assert! m'.isMVar
    IO.println (← getExprMVarAssignment? m'.mvarId!)
    IO.println (← getExprMVarAssignment? m.mvarId!)
    IO.println (← ppExpr (← instantiateMVars b))
    IO.println (← ppExpr m)
    return ()

#eval tst
