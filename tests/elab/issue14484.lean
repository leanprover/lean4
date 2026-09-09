import Lean
open Lean

private def cachePrimingType : Expr :=
  let falseE := mkConst ``False
  let falseToFalse := .forallE `h falseE falseE .default
  let identity := .lam `h falseE (.bvar 0) .default
  .app (.lam `_ falseToFalse falseE .default) identity

/--
info: kernel accepted opaqueFVarCacheFalse : False
---
error: (kernel) declaration has free variables 'opaqueFVarCacheFalse', expression: ⏎
  _kernel_fresh.2
-/
#guard_msgs in
run_meta
  let name := `opaqueFVarCacheFalse
  addDecl <| .opaqueDecl {
    name
    levelParams := []
    type := cachePrimingType
    value := .fvar { name := .num `_kernel_fresh 2 }
    isUnsafe := false
  }
  logInfo m!"kernel accepted {name} : False"

theorem assumptionFreeFalse : False := opaqueFVarCacheFalse

/-- info: 'opaqueFVarCacheFalse' depends on axioms: [opaqueFVarCacheFalse, sorryAx] -/
#guard_msgs in
#print axioms opaqueFVarCacheFalse
/-- info: 'assumptionFreeFalse' depends on axioms: [assumptionFreeFalse] -/
#guard_msgs in
#print axioms assumptionFreeFalse
