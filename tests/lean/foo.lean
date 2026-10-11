import Lean

open Lean Meta

/-
This code currently compiles to a chain of a lot of inc/dec. If we could infer
Lean.Expr.cleanupAnnotations to be a pseudo projection it should be possible to just do this
-/

set_option trace.Compiler.saveImpure true in
def test (type : Expr) : MetaM Unit := do
    let_expr Eq _ _ rhs := type | return ()
    let_expr HAdd.hAdd _ _ _ _ _ rhs := rhs | return ()
    let_expr OfNat.ofNat _ rhs _ := rhs | return ()
    let some 1 := getRawNatValue? rhs | return ()

    logInfo "ah"

