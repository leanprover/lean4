/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Transform
import Lean.Meta.Check
import Lean.Compiler.LCNF
import Lean.Compiler.Check
import Lean.Compiler.CompilerM

namespace Lean.Compiler

/--
Declaration being processed by the Lean to Lean compiler passes.
-/
structure Decl where
  /--
  The name of the declaration from the `Environment` it came from
  -/
  name  : Name
  /--
  The type of the declaration. Note that this is an erased LCNF type
  instead of the fully dependent one that might have been the original
  type of the declaration in the `Environment`.
  -/
  type  : Expr
  /--
  The value of the declaration, usually changes as it progresses
  through compiler passes.
  -/
  value : Expr

/--
Inline constants tagged with the `[macroInline]` attribute occurring in `e`.
-/
def macroInline (e : Expr) : CoreM Expr :=
  Core.transform e fun e => do
    let .const declName us := e.getAppFn | return .visit e
    unless hasMacroInlineAttribute (← getEnv) declName do return .visit e
    let val ← Core.instantiateValueLevelParams (← getConstInfo declName) us
    return .visit <| val.beta e.getAppArgs

/--
Replace nested occurrences of `unsafeRec` names with the safe ones.
-/
private def replaceUnsafeRecNames (value : Expr) : CoreM Expr :=
  Core.transform value fun e =>
    match e with
    | .const declName us =>
      if let some safeDeclName := isUnsafeRecName? declName then
        return .done (.const safeDeclName us)
      else
        return .done e
    | _ => return .visit e

/--
Convert the given declaration from the Lean environment into `Decl`.
The steps for this are roughly:
- partially erasing type information of the declaration
- eta-expanding the declaration value.
- if the declaration has an unsafe-rec version, use it.
- expand declarations tagged with the `[macroInline]` attribute
- turn the resulting term into LCNF
-/
def toDecl (declName : Name) : CoreM Decl := do
  let env ← getEnv
  let some info := env.find? (mkUnsafeRecName declName) <|> env.find? declName | throwError "declaration `{declName}` not found"
  let some value := info.value? | throwError "declaration `{declName}` does not have a value"
  Meta.MetaM.run' do
    let type  ← toLCNFType info.type
    let value ← Meta.lambdaTelescope value fun xs body => do Meta.mkLambdaFVars xs (← Meta.etaExpand body)
    let value ← replaceUnsafeRecNames value
    let value ← macroInline value
    let value ← toLCNF value
    return { name := declName, type, value }

def Decl.check (decl : Decl) (cfg : Check.Config := {}): CoreM Unit := do
  Compiler.check decl.value cfg { lctx := {} }
  let valueType ← InferType.inferType decl.value { lctx := {} }
  unless compatibleTypes decl.type valueType do
    throwError "declaration type mismatch at `{decl.name}`, value has type{indentExpr valueType}\nbut is expected to have type{indentExpr decl.type}"

/-- Apply `f` to declaration `value`. -/
def Decl.mapValue (decl : Decl) (f : Expr → CompilerM Expr) : CoreM Decl := do
  return { decl with value := (← f decl.value |>.run' { nextIdx := (← getMaxLetVarIdx decl.value) + 1 }) }

end Lean.Compiler
