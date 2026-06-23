/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

prelude
public import Lean.Elab.ConfigEval.Basic
import Lean.Elab.ConfigEval.Util
public import Lean.Elab.Command
import Lean.Elab.DeclNameGen
import all Lean.Elab.ErrorUtils
public import Lean.Meta.Eval

public section

namespace Lean.Elab.ConfigEval

open Meta Term Command

namespace EvalExpr

def withSimpleEvalExpr {α : Type} (c : Name) (evalExprImpl : String → Array Expr → MetaM α) : Expr → MetaM α :=
  withWHNF (errMsg := m!"\nExpecting `{.ofConstName c}`.") fun e => do
    let some ctor := e.getAppFn.constName? | throwUnsupportedExpr
    let Name.str c' s := ctor | throwUnsupportedExpr
    unless (c == c') do throwUnsupportedExpr
    evalExprImpl s e.getAppArgs

end EvalExpr

open EvalExpr

/--
Ensures an `EvalExpr` instance exists for the given type by deriving one if necessary.
Derivation can handle `EvalExpr` instance for nonrecursive inductive types without universes, parameters, or indices,
and which only does simple recursion.
-/
def ensureEvalExpr
    (vis? : Option (TSyntax `Lean.Parser.Command.visibility))
    (kind : TSyntax `Lean.Parser.Term.attrKind)
    (cmdRef typeRef : Syntax) (type : Expr) : CommandElabM Unit := do
  withClassInstDeps ``EvalExpr type extraDeps fun type' => withRef cmdRef do
    let ival ← getIndType type'
    let indTypeIdent := mkCIdentFrom typeRef ival.name
    let instName ← NameGen.mkBaseNameWithSuffix' "inst" #[] <| ← ``(EvalExpr $indTypeIdent)
    let evalExprDef := mkIdent (instName ++ Name.mkSimple "evalExpr")
    let mut exprCases : Array (String × Term) := #[]
    for ctorName in ival.ctors do
      if useCtor ival ctorName then
        let (xs, _, _) ← forallMetaTelescopeReducing (← inferType (mkConst ctorName))
        let .str _ ctorName' := ctorName | unreachable!
        let vs ← xs.mapM fun _ => mkIdent <$> Core.mkFreshUserName `v
        let val ← `(pure ($(mkCIdent ctorName) $vs*))
        let recArgs ← xs.mapM fun x => return (← instantiateMVars (← inferType x)) == type'
        let val ← (((Array.range xs.size).zip recArgs).zip vs).foldrM (init := val) fun ((idx, recArg), v) val =>
          if recArg then
            `($evalExprDef args[$(quote idx)]! >>= fun $v => $val)
          else
            `(EvalExpr.evalExpr args[$(quote idx)]! >>= fun $v => $val)
        let val ← `(guard (args.size == $(quote xs.size)) *> $val)
        exprCases := exprCases.push (ctorName', val)
    let exprMatcher ← makeStringMatcher (← `(ident| ctor)) exprCases (← `(throwUnsupportedExpr))
    `($[$vis?:visibility]? partial def $evalExprDef : Expr → MetaM $indTypeIdent :=
        withSimpleEvalExpr $(quote ival.name) fun ctor args => $exprMatcher
      $[$vis?:visibility]? $kind:attrKind instance%$cmdRef $(mkIdentFrom cmdRef instName (canonical := type == type')):ident : EvalExpr $indTypeIdent where
        evalExpr := $evalExprDef
        expectedType? := some (Expr.const $(quote ival.name) []))
where
  getIndType (type : Expr) : TermElabM InductiveVal := withRef typeRef do
    let some indTypeName := (← whnfR type).constName?
      | throwError "`{type}` is not a constant"
    let .inductInfo ival ← getConstInfo indTypeName
      | throwError "`{.ofConstName indTypeName}` is not an inductive type"
    unless ival.levelParams.isEmpty && ival.numParams == 0 && ival.numIndices == 0 do
      throwError "`{.ofConstName indTypeName}` has universe parameters, parameters, or indices"
    if ival.isNested || ival.isReflexive then
      throwError "`{.ofConstName indTypeName}` has unsupported recursion"
    return ival
  useCtor (ival : InductiveVal) (ctorName : Name) : Bool :=
    ctorName.isStr && !ctorName.hasMacroScopes && !isPrivateName ctorName && ctorName.getPrefix == ival.name
  extraDeps (type : Expr) : TermElabM (Array Expr) := withRef typeRef do
    let ival ← getIndType type
    let mut deps := #[]
    for ctorName in ival.ctors do
      if useCtor ival ctorName then
        let (xs, bis, _) ← forallMetaTelescopeReducing (← inferType (mkConst ctorName))
        unless bis.all (·.isExplicit) do
          throwError "Every field of `{.ofConstName ctorName}` must be explicit"
        for x in xs do
          let xTy ← inferType x
          if xTy.hasMVar then
            throwError "Field `{x}` of `{.ofConstName ctorName}` is dependent"
          if xTy == type then
            continue
          deps := deps.push xTy
    return deps

@[expose] unsafe def evalMetaEval (α : Type) (typeName : Name) (moduleName? : Option Name) (e : Expr) : MetaM α := do
  unless (← getEnv).contains typeName do
    let fromMsg := if let some moduleName := moduleName? then m!" (from `{moduleName}`)" else m!""
    throwError m!"Error evaluating configuration: the type `{typeName}`{fromMsg} is not in scope here"
  recordExtraModUseFromDecl (isMeta := true) typeName
  let eType ← inferType e
  unless ← isDefEqGuarded (mkConst typeName) eType do
    throwError "Type mismatch. Option value{inlineExpr e}{← mkHasTypeButIsExpectedMsg eType (mkConst typeName)}"
  try
    withoutModifyingEnv <| Meta.evalExpr' α typeName e (safety := .partial)
  catch ex =>
    throwError m!"Error evaluating{indentExpr e}\n\nException: {ex.toMessageData}"

/-- Creates an `EvalExpr` instance that uses `Meta.evalExpr` to compile and evaluate the expression. -/
def deriveEvalExprUsingMetaEval
    (vis? : Option (TSyntax `Lean.Parser.Command.visibility))
    (kind : TSyntax `Lean.Parser.Term.attrKind)
    (cmdRef typeRef : Syntax) (type : Expr) : CommandElabM Unit := do
  let cmd ← liftTermElabM <| withFreshMacroScope do
    let Expr.const typeName [] := type
      | throwErrorAt typeRef "Expecting a constant with no universes, not `{type}`"
    let env ← getEnv
    let moduleName? := (env.header.moduleNames[·]!) <$> env.getModuleIdxFor? typeName
    let typeId := mkCIdentFrom typeRef typeName
    `($[$vis?:visibility]? $kind:attrKind instance%$cmdRef : EvalExpr @$typeId where
        evalExpr := unsafe evalMetaEval @$typeId $(quote typeName) $(quote moduleName?)
        expectedType? := some (mkConst @$(quote typeName)))
  elabCommand cmd

end Lean.Elab.ConfigEval
