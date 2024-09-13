import Lean

open Lean Meta

#eval show MetaM _ from do
  let e : Expr := .const ``Bool.true []
  let m₁ ← withNewMCtxDepth <| mkFreshExprMVar (Expr.const ``Bool [])
  guard <|← isDefEq e m₁
