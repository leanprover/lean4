import Lean
open Lean
open Lean.Meta

def tst1 : MetaM Unit := do
  withLocalDeclD `x (mkConst ``Nat) fun x =>
  withLocalDeclD `y (mkConst ``Nat) fun y => do
    let e ← mkForallFVars #[y, x] (← mkEq (← mkAdd x (← mkAdd x y)) x)
    IO.println (← Meta.ppExpr e)

#eval tst1

def tst2 : MetaM Unit := do
  let x ← mkFreshExprMVar (mkConst ``Nat) (userName := `x)
  let y ← mkFreshExprMVar (mkConst ``Nat) (userName := `y)
  let e ← mkForallFVars #[y, x] (← mkEq (← mkAdd x (← mkAdd x y)) x) (binderInfoForMVars := BinderInfo.default)
  IO.println (← Meta.ppExpr e)

#eval tst2

def tst3 : MetaM Unit := do
  let x ← mkFreshExprMVar (mkConst ``Nat) (userName := `x)
  let y ← mkFreshExprMVar (mkConst ``Nat) (userName := `y)
  withLocalDeclD `h (← mkEq x y) fun h => do
    let e ← mkForallFVars #[y, x, h] (← mkEq (← mkAdd x (← mkAdd x y)) x)
    IO.println (← Meta.ppExpr e)

#eval tst3

def tst4 : MetaM Unit := do
  let x ← mkFreshExprMVar (mkConst ``Nat) (userName := `x)
  let y ← mkFreshExprMVar (mkConst ``Nat) (userName := `y)
  withLocalDeclD `h (← mkEq x y) fun h => do
    let z ← mkFreshExprMVar (mkConst ``Nat) (userName := `z)
    let e ← mkLambdaFVars #[y, x, h, z] (← mkAdd z (← mkAdd x y)) (binderInfoForMVars := BinderInfo.default)
    IO.println (← Meta.ppExpr e)

set_option pp.funBinderTypes true
#eval tst4
