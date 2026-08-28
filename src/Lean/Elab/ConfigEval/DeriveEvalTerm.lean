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

public section

namespace Lean.Elab.ConfigEval

open Meta Term Command

namespace EvalTerm

/--
Resolves `id`, making sure the result is in namespace `c`.
Returns `s` if the resolved name is of the form of the form `Name.str c s`.
-/
private def resolveAtomicNameForConstNamespace (c : Name) (id : Ident) : TermElabM String := do
  let n := id.getId.eraseMacroScopes
  -- For atomic names, resolve them as if `c` is the namespace.
  if let Name.str Name.anonymous s := n then
    let n' := Name.str c s
    if (← getEnv).contains n' then
      if (← getInfoState).enabled then
        addConstInfo id n'
      return s
  let n ← realizeGlobalConstNoOverloadWithInfo id
  if !n.hasMacroScopes && n.getPrefix == c then
    if let Name.str _ s := n then
      return s
  throwUnsupportedSyntax

/--
Resolves `id` as if it were a dotted identifier for namespace `c`,
and returns `s` if the resolved name is of the form `Name.str c s`.
-/
private def resolveDottedAtomicNameForConstNamespace (c : Name) (id : Ident) : TermElabM String := do
  let n := id.getId.eraseMacroScopes
  if let Name.str Name.anonymous s := n then
    addCompletionInfo <| CompletionInfo.dotId id n {} (← mkConstWithLevelParams c)
    let n' := Name.str c s
    if (← getEnv).contains n' then
      if (← getInfoState).enabled then
        addConstInfo id n'
      return s
    else
      resolveAtomicNameForConstNamespace c (mkIdentFrom id n')
  else
    throwUnsupportedSyntax

/--
Wrapper to handle atomic identifiers and dotted identifiers.
-/
partial def withSimpleEvalStx {α} (indTypeName : Name) (evalStxImpl : String → TSyntaxArray `term → TermElabM (α × Expr)) : Term → TermElabM (α × Expr) :=
  evalTermWithInfo (Expr.const indTypeName []) fun
  | `($f:ident) => do
    let ctorName ← resolveAtomicNameForConstNamespace indTypeName f
    evalStxImpl ctorName #[]
  | `($f:ident $args*) => do
    let ctorName ← resolveAtomicNameForConstNamespace indTypeName f
    evalStxImpl ctorName args
  | `(.$f:ident) => do
    let ctorName ← resolveDottedAtomicNameForConstNamespace indTypeName f
    evalStxImpl ctorName #[]
  | `(.$f:ident $args*) => do
    let ctorName ← resolveDottedAtomicNameForConstNamespace indTypeName f
    evalStxImpl ctorName args
  | _ => throwUnsupportedSyntax

def checkExpectedNumberOfArguments (ctor : Name) (expected : Nat) (args : TSyntaxArray `term) : TermElabM Unit := do
  unless expected == args.size do
    throwError "unexpected number of arguments, `{.ofConstName ctor}` expects {expected} argument{expected.plural}, \
      but {args.size} {args.size.plural "was" "were"} provided"

end EvalTerm

open EvalTerm

/--
Ensures an `EvalTerm` instance exists for the given type by deriving one if necessary.
Derivation can handle `EvalTerm` instance for inductive types without universes, parameters, or indices,
and which only does simple recursion.
-/
def ensureEvalTerm
    (vis? : Option (TSyntax `Lean.Parser.Command.visibility))
    (kind : TSyntax `Lean.Parser.Term.attrKind)
    (cmdRef typeRef : Syntax) (type : Expr) : CommandElabM Unit := do
  withClassInstDeps ``EvalTerm type extraDeps fun type' => withRef cmdRef do
    let ival ← getIndType type'
    let indTypeIdent := mkCIdentFrom typeRef ival.name
    let instName ← NameGen.mkBaseNameWithSuffix' "inst" #[] <| ← ``(EvalTerm $indTypeIdent)
    let evalTermDef := mkIdent (instName ++ Name.mkSimple "evalTerm")
    let mut stxCases : Array (String × Term) := #[]
    for ctorName in ival.ctors do
      if useCtor ival ctorName then
        let (xs, _, _) ← forallMetaTelescopeReducing (← inferType (mkConst ctorName))
        let .str _ ctorName' := ctorName | unreachable!
        let vs ← xs.mapM fun _ => mkIdent <$> Core.mkFreshUserName `v
        let es ← xs.mapM fun _ => mkIdent <$> Core.mkFreshUserName `e
        let expr ← `(Expr.const $(quote ctorName) [])
        let expr ← es.foldlM (init := expr) fun expr e => `(Expr.app $expr $e)
        let val ← `(pure ($(mkCIdent ctorName) $vs*, $expr))
        let recArgs ← xs.mapM fun x => return (← instantiateMVars (← inferType x)) == type'
        let val ← (((Array.range xs.size).zip recArgs).zip (vs.zip es)).foldrM (init := val) fun ((idx, recArg), v, e) val =>
          if recArg then
            `($evalTermDef args[$(quote idx)]! >>= fun ($v, $e) => $val)
          else
            `(EvalTerm.evalTerm args[$(quote idx)]! >>= fun ($v, $e) => $val)
        let val ← `(checkExpectedNumberOfArguments $(quote ctorName) $(quote xs.size) args *> $val)
        stxCases := stxCases.push (ctorName', val)
    let stxMatcher ← makeStringMatcher (← `(ident| ctor)) stxCases (← `(throwUnsupportedSyntax))
    `($[$vis?:visibility]? partial def $evalTermDef : Term → TermElabM ($indTypeIdent × Expr) :=
        withSimpleEvalStx $(quote ival.name) fun ctor args => $stxMatcher
      $[$vis?:visibility]? $kind:attrKind instance%$cmdRef $(mkIdentFrom cmdRef instName (canonical := type == type')):ident : EvalTerm $indTypeIdent where
        evalTerm := $evalTermDef
        typeExpr := Expr.const $(quote ival.name) [])
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

end Lean.Elab.ConfigEval
