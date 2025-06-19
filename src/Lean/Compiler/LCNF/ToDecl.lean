/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Transform
import Lean.Meta.Match.MatcherInfo
import Lean.Compiler.ExternAttr
import Lean.Compiler.InitAttr
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.LCNF.ToLCNF

namespace Lean.Compiler.LCNF
/--
Inline constants tagged with the `[macro_inline]` attribute occurring in `e`.
-/
def macroInline (e : Expr) : CoreM Expr :=
  Core.transform e fun e => do
    let .const declName us := e.getAppFn | return .continue
    unless hasMacroInlineAttribute (← getEnv) declName do return .continue
    let val ← Core.instantiateValueLevelParams (← getConstInfo declName) us
    return .visit <| val.beta e.getAppArgs

private def normalizeAlt (e : Expr) (numParams : Nat) : MetaM Expr :=
  Meta.lambdaTelescope e fun xs body => do
    if xs.size == numParams then
      return e
    else if xs.size > numParams then
      let body ← Meta.mkLambdaFVars xs[numParams:] body
      let body ← Meta.withLetDecl (← mkFreshUserName `_k) (← Meta.inferType body) body fun x => Meta.mkLetFVars #[x] x
      Meta.mkLambdaFVars xs[:numParams] body
    else
      Meta.forallBoundedTelescope (← Meta.inferType e) (numParams - xs.size) fun ys _ =>
        Meta.mkLambdaFVars (xs ++ ys) (mkAppN e ys)

/--
Inline auxiliary `matcher` applications.
-/
partial def inlineMatchers (e : Expr) : CoreM Expr :=
  Meta.MetaM.run' <| Meta.transform e fun e => do
    let .const declName us := e.getAppFn | return .continue
    let some info ← Meta.getMatcherInfo? declName | return .continue
    let numArgs := e.getAppNumArgs
    if numArgs > info.arity then
      return .continue
    else if numArgs < info.arity then
      Meta.forallBoundedTelescope (← Meta.inferType e) (info.arity - numArgs) fun xs _ =>
        return .visit (← Meta.mkLambdaFVars xs (mkAppN e xs))
    else
      let mut args := e.getAppArgs
      let numAlts := info.numAlts
      let altNumParams := info.altNumParams
      let rec inlineMatcher (i : Nat) (args : Array Expr) (letFVars : Array Expr) : MetaM Expr := do
        if h : i < numAlts then
          let altIdx := i + info.getFirstAltPos
          let numParams := altNumParams[i]
          let alt ← normalizeAlt args[altIdx]! numParams
          Meta.withLetDecl (← mkFreshUserName `_alt) (← Meta.inferType alt) alt fun altFVar =>
            inlineMatcher (i+1) (args.set! altIdx altFVar) (letFVars.push altFVar)
        else
          let info ← getConstInfo declName
          let value := (← Core.instantiateValueLevelParams info us).beta args
          Meta.mkLetFVars letFVars value
      return .visit (← inlineMatcher 0 args #[])

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
    | _ => return .continue

/--
Return the declaration `ConstantInfo` for the code generator.

Remark: the unsafe recursive version is tried first.
-/
def getDeclInfo? (declName : Name) : CoreM (Option ConstantInfo) := do
  let env ← getEnv
  return env.find? (mkUnsafeRecName declName) <|> env.find? declName

/--
Convert the given declaration from the Lean environment into `Decl`.
The steps for this are roughly:
- partially erasing type information of the declaration
- eta-expanding the declaration value.
- if the declaration has an unsafe-rec version, use it.
- expand declarations tagged with the `[macro_inline]` attribute
- turn the resulting term into LCNF declaration
-/
def toDecl (declName : Name) : CompilerM Decl := do
  let declName := if let some name := isUnsafeRecName? declName then name else declName
  let some info ← getDeclInfo? declName | throwError "declaration `{declName}` not found"
  let safe := !info.isPartial && !info.isUnsafe
  let env ← getEnv
  let inlineAttr? := getInlineAttribute? env declName
  let paramsFromTypeBinders (expr : Expr) : CompilerM (Array Param) := do
    let mut params := #[]
    let mut currentExpr := expr
    repeat
      match currentExpr with
      | .forallE binderName type body _ =>
        let borrow := isMarkedBorrowed type
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
    let some value := info.value? (allowOpaque := true) | throwError "declaration `{declName}` does not have a value"
    let (type, value) ← Meta.MetaM.run' do
      let type  ← toLCNFType info.type
      let value ← Meta.lambdaTelescope value fun xs body => do Meta.mkLambdaFVars xs (← Meta.etaExpand body)
      let value ← replaceUnsafeRecNames value
      let value ← macroInline value
      /- Recall that some declarations tagged with `macro_inline` contain matchers. -/
      let value ← inlineMatchers value
      /- Recall that `inlineMatchers` may have exposed `ite`s and `dite`s which are tagged as `[macro_inline]`. -/
      let value ← macroInline value
      return (type, value)
    let code ← toLCNF value
    let decl ← if let .fun decl (.return _) := code then
      eraseFunDecl decl (recursive := false)
      pure { name := declName, params := decl.params, type, value := .code decl.value, levelParams := info.levelParams, safe, inlineAttr? : Decl }
    else
      pure { name := declName, params := #[], type, value := .code code, levelParams := info.levelParams, safe, inlineAttr? }
    /- `toLCNF` may eta-reduce simple declarations. -/
    decl.etaExpand

end Lean.Compiler.LCNF
