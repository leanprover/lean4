/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Simp.Attr
import Lean.Meta.Tactic.Simp.Simproc

namespace Lean.Meta.Grind
open Simp

builtin_initialize grindNormExt : SimpExtension ←
  registerSimpAttr `grind_norm "simplification/normalization theorems for `grind`"

builtin_initialize grindNormSimprocExt : SimprocExtension ←
  registerSimprocAttr `grind_norm_proc "simplification/normalization procedured for `grind`" none

builtin_initialize grindCasesExt : SimpleScopedEnvExtension Name NameSet ←
  registerSimpleScopedEnvExtension {
    initial        := {}
    addEntry       := fun s declName => s.insert declName
  }

/--
Returns `true` if `declName` has been tagged with attribute `[grind_cases]`.
-/
def isGrindCasesTarget (declName : Name) : CoreM Bool :=
  return grindCasesExt.getState (← getEnv) |>.contains declName

private def getAlias? (value : Expr) : MetaM (Option Name) :=
  lambdaTelescope value fun _ body => do
    if let .const declName _ := body.getAppFn' then
      return some declName
    else
      return none

/--
Throws an error if `declName` cannot be annotated with attribute `[grind_cases]`.
We support the following cases:
- `declName` is a non-recursive datatype.
- `declName` is an abbreviation for a non-recursive datatype.
-/
private partial def validateGrindCasesAttr (declName : Name) : CoreM Unit := do
  match (← getConstInfo declName) with
  | .inductInfo info =>
    if info.isRec then
      throwError "`{declName}` is a recursive datatype"
  | .defnInfo info =>
    let failed := throwError "`{declName}` is a definition, but it is not an alias/abbreviation for an inductive datatype"
    let some declName ← getAlias? info.value |>.run' {} {}
      | failed
    try
      validateGrindCasesAttr declName
    catch _ =>
      failed
  | _ =>
    throwError "`{declName}` is not an inductive datatype or an alias for one"

builtin_initialize
  registerBuiltinAttribute {
    name  := `grind_cases
    descr := "`grind` tactic applies `cases` to (non-recursive) inductives during pre-processing step"
    add   := fun declName _ attrKind => do
      validateGrindCasesAttr declName
      grindCasesExt.add declName attrKind
  }

end Lean.Meta.Grind
