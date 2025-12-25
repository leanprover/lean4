import Lean.Meta.Tactic.Grind
import Lean.Meta.Sym.Main
open Lean Meta Grind Sym
set_option grind.debug true

def test : GrindM Unit := do
  let f  ← mkConstS `f
  let f₁ := mkConst `f
  let f₂ ← mkConstS `f
  assert! isSameExpr f f₂
  assert! !isSameExpr f f₁
  let x₁ ← mkBVarS 0
  let x₂ ← mkBVarS 0
  assert! isSameExpr
    (← mkLambdaS `x .default (← mkConstS ``Nat) (← mkMDataS {} (← mkProjS ``Prod 0 (← mkAppS f x₁))))
    (← mkLambdaS `y .default (← mkConstS ``Nat) (← mkMDataS {} (← mkProjS ``Prod 0 (← mkAppS f₂ x₂))))
  assert! !isSameExpr (← mkAppS f x₁) (mkApp f x₁)
  assert!
    mkLambda `x .default (mkConst ``Nat) (mkMData {} (mkProj ``Prod 0 (mkApp f x₁)))
    ==
    (← mkLambdaS `y .default (← mkConstS ``Nat) (← mkMDataS {} (← mkProjS ``Prod 0 (← mkAppS f₂ x₂))))

#eval SymM.run' do
  test
