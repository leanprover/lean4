/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Transform
import Lean.Compiler.LCNF

namespace Lean.Compiler

/--
Declaration being processed by the Lean to Lean compiler passes.
-/
structure Decl where
  name  : Name
  type  : Expr
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

Remarks:
- If the declaration has an unsafe-rec version, we use it.
- We eta-expand the declaration value.
- We expand declarations tagged with the `[MacroInline]` attribute
-/
def toDecl (declName : Name) : CoreM Decl := do
  let env ← getEnv
  let some info := env.find? (mkUnsafeRecName declName) <|> env.find? declName | throwError "declaration `{declName}` not found"
  let some value := info.value? | throwError "declaration `{declName}` does not have a value"
  Meta.MetaM.run' do
    let value ← Meta.lambdaTelescope value fun xs body => do Meta.mkLambdaFVars xs (← Meta.etaExpand body)
    let value ← replaceUnsafeRecNames value
    let value ← macroInline value
    let value ← toLCNF {} value
    return { name := declName, type := info.type, value }

end Lean.Compiler
