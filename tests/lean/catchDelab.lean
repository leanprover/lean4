import Lean

@[delab app]
partial def Lean.PrettyPrinter.Delaborator.delabThrow : Delab := do
  let e ← SubExpr.getExpr
  let ty ← Meta.inferType e
  failure

#check test
