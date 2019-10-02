import init.lean
open Lean

#eval (Expr.fvar `a).hasFVar
#eval (Expr.app (Expr.const `foo []) (Expr.fvar `a)).hasFVar
#eval (Expr.app (Expr.const `foo []) (Expr.const `a [])).hasFVar

#eval (Expr.mvar `a).hasMVar
#eval (Expr.app (Expr.const `foo []) (Expr.mvar `a)).hasMVar
#eval (Expr.app (Expr.const `foo []) (Expr.const `a [])).hasMVar
