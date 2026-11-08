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
error: (kernel) (InLean) unexpected free variable in value of opaqueFVarCacheFalse
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

/-- error: (kernel) (InLean) type mismatch in theorem assumptionFreeFalse -/
#guard_msgs in
theorem assumptionFreeFalse : False := opaqueFVarCacheFalse

/-- info: 'opaqueFVarCacheFalse' depends on axioms: [opaqueFVarCacheFalse, sorryAx] -/
#guard_msgs in
#print axioms opaqueFVarCacheFalse
/-- info: 'assumptionFreeFalse' depends on axioms: [assumptionFreeFalse] -/
#guard_msgs in
#print axioms assumptionFreeFalse
