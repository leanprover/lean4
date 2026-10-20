/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Compiler.InitAttr
public import Lean.Compiler.LCNF.ToLCNF
import Lean.Compiler.Options
import Lean.Meta.Transform
import Lean.Meta.Match.MatcherInfo
import Init.While
import Lean.Compiler.ExportAttr

public section

namespace Lean.Compiler.LCNF

/--
Return the declaration `ConstantInfo` for the code generator.

Remark: the unsafe recursive version is tried first.
-/
def getDeclInfo? (declName : Name) : CoreM (Option ConstantInfo) := do
  let env ← getEnv
  return env.find? (mkUnsafeRecName declName) <|> env.find? declName

def declIsNotUnsafe (declName : Name) : CoreM Bool := do
  let env ← getEnv
  let some info := env.find? declName | return true
  if info.isUnsafe then
    return false
  else
    if info matches .opaqueInfo .. then
      -- check if its a partial def
      return env.find? (Compiler.mkUnsafeRecName declName) |>.isNone
    else
      return true

/--
Convert the given declaration from the Lean environment into `Decl`.
The steps for this are roughly:
- partially erasing type information of the declaration
- eta-expanding the declaration value.
- if the declaration has an unsafe-rec version, use it.
- expand declarations tagged with the `[macro_inline]` attribute
- turn the resulting term into LCNF declaration
-/
def toDecl (declName : Name) : CompilerM (Decl .pure) := do
  let declName := if let some name := isUnsafeRecName? declName then name else declName
  let some info ← getDeclInfo? declName | throwError "declaration `{.ofConstName declName}` not found"
  let safe ← declIsNotUnsafe declName
  let env ← getEnv
  let inlineAttr? := getInlineAttribute? env declName
  let paramsFromTypeBinders (expr : Expr) : CompilerM (Array (Param .pure)) := do
    let mut params := #[]
    let mut currentExpr := expr
    let ignoreBorrow := compiler.ignoreBorrowAnnotation.get (← getOptions)
    repeat
      match currentExpr with
      | .forallE binderName type body _ =>
        let borrow := !ignoreBorrow && isMarkedBorrowed type
        params := params.push (← mkParam binderName type borrow)
        currentExpr := body
      | _ => break
    return params
  if let some externAttrData := getExternAttrData? env declName then
    let type ← Meta.MetaM.run' (toLCNFType info.type)
    let params ← paramsFromTypeBinders type
    return { name := declName, params, type, value := .extern externAttrData, levelParams := info.levelParams, safe, inlineAttr? }
  else if hasInitAttr env declName then
    let type ← Meta.MetaM.run' (toLCNFType info.type)
    let params ← paramsFromTypeBinders type
    return { name := declName, params, type, value := .extern { entries := [] }, levelParams := info.levelParams, safe, inlineAttr? }
  else
    let some value := info.value? (allowOpaque := true) | throwError "declaration `{.ofConstName declName}` does not have a value"
    let (type, value) ← Meta.MetaM.run' do
      let type  ← toLCNFType info.type
      let value ← Meta.lambdaTelescope value fun xs body => do Meta.mkLambdaFVars xs (← Meta.etaExpand body)
      return (type, value)
    let code ← toLCNF value type
    let mut decl ← if let .fun decl (.return _) := code then
      eraseFunDecl decl (recursive := false)
      pure { name := declName, params := decl.params, type, value := .code decl.value, levelParams := info.levelParams, safe, inlineAttr? : Decl .pure }
    else
      pure { name := declName, params := #[], type, value := .code code, levelParams := info.levelParams, safe, inlineAttr? }
    /- `toLCNF` may eta-reduce simple declarations. -/
    decl ← decl.etaExpand
    if compiler.ignoreBorrowAnnotation.get (← getOptions) then
      decl := { decl with params := ← decl.params.mapM (·.updateBorrow false) }
    if isExport env decl.name && decl.params.any (·.borrow) then
      throwError m!" Declaration {decl.name} is marked as `export` but some of its parameters have borrow annotations.\n Consider using `set_option compiler.ignoreBorrowAnnotation true in` to suppress the borrow annotations in its type.\n If the declaration is part of an `export`/`extern` pair make sure to also suppress the annotations at the `extern` declaration."
    return decl

end Lean.Compiler.LCNF
