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
import Lean.Compiler.JoinPoints

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



/--
Join points are let bound variables with an _jp name prefix.
They always need to satisfy two conditions:
1. Be fully applied
2. Always be called in tail position
in order to allow the optimizer to turn them into efficient machine code.
This function ensures that inside the given declaration both of these
conditions are satisfied and throws an exception otherwise.
-/
def Decl.checkJoinPoints (decl : Decl) : CompilerM Unit :=
  JoinPointChecker.checkJoinPoints decl.value


/--
Check whether a declaration still fulfills all the invariants that we put
on them, if it does not throw an exception. This is meant as a sanity
check for the code generator itself, not to find errors in the user code.

These invariants are:
- The ones enforced by `Compiler.check`
- The stored and the inferred LCNF type of the declaration are compatible according to `compatibleTypes`
-/
def Decl.check (decl : Decl) (cfg : Check.Config := {}): CoreM Unit := do
  Compiler.check decl.value cfg { lctx := {} }
  checkJoinPoints decl |>.run' {}
  let valueType ← InferType.inferType decl.value { lctx := {} }
  unless compatibleTypes decl.type valueType do
    throwError "declaration type mismatch at `{decl.name}`, value has type{indentExpr valueType}\nbut is expected to have type{indentExpr decl.type}"

/-- Apply `f` to declaration `value`. -/
def Decl.mapValue (decl : Decl) (f : Expr → CompilerM Expr) : CoreM Decl := do
  return { decl with value := (← f decl.value |>.run' { nextIdx := (← getMaxLetVarIdx decl.value) + 1 }) }

def Decl.toString (decl : Decl) : CoreM String := do
  Meta.MetaM.run' do
    return s!"{decl.name} : {← Meta.ppExpr decl.type} :=\n{← Meta.ppExpr decl.value}"

end Lean.Compiler
