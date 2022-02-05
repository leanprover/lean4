import Lean

open Lean
open Lean.Meta

def test (f : Expr) : MetaM Unit := do
  let some thm  ← mkCongrSimp? f | unreachable!
  check thm.type
  check thm.proof
  assert! (← isDefEq thm.type (← inferType thm.proof))
  IO.println (← Meta.ppExpr thm.type)

#eval test (mkConst ``decide)
#eval test (mkConst ``Array.uget [levelZero])
