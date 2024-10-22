/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Diagnostics
import Lean.Elab.Open
import Lean.Elab.SetOption
import Lean.Elab.Eval

namespace Lean.Elab.Term
open Meta

@[builtin_term_elab «prop»] def elabProp : TermElab := fun _ _ =>
  return mkSort levelZero

private def elabOptLevel (stx : Syntax) : TermElabM Level :=
  if stx.isNone then
    pure levelZero
  else
    elabLevel stx[0]

@[builtin_term_elab «sort»] def elabSort : TermElab := fun stx _ =>
  return mkSort (← elabOptLevel stx[1])

@[builtin_term_elab «type»] def elabTypeStx : TermElab := fun stx _ =>
  return mkSort (mkLevelSucc (← elabOptLevel stx[1]))

/-!
 the method `resolveName` adds a completion point for it using the given
    expected type. Thus, we propagate the expected type if `stx[0]` is an identifier.
    It doesn't "hurt" if the identifier can be resolved because the expected type is not used in this case.
    Recall that if the name resolution fails a synthetic sorry is returned.-/

@[builtin_term_elab «pipeCompletion»] def elabPipeCompletion : TermElab := fun stx expectedType? => do
  let e ← elabTerm stx[0] none
  unless e.isSorry do
    addDotCompletionInfo stx e expectedType?
  throwErrorAt stx[1] "invalid field notation, identifier or numeral expected"

@[builtin_term_elab «completion»] def elabCompletion : TermElab := fun stx expectedType? => do
  /- `ident.` is ambiguous in Lean, we may try to be completing a declaration name or access a "field". -/
  if stx[0].isIdent then
    -- Add both an `id` and a `dot` `CompletionInfo` and have the language server figure out which
    -- one to use.
    addCompletionInfo <| CompletionInfo.id stx stx[0].getId (danglingDot := true) (← getLCtx) expectedType?
    let s ← saveState
    try
      let e ← elabTerm stx[0] none
      addDotCompletionInfo stx e expectedType?
    catch _ =>
      s.restore
    throwErrorAt stx[1] "invalid field notation, identifier or numeral expected"
  else
    elabPipeCompletion stx expectedType?

@[builtin_term_elab «hole»] def elabHole : TermElab := fun stx expectedType? => do
  let kind := if (← read).inPattern || !(← read).holesAsSyntheticOpaque then MetavarKind.natural else MetavarKind.syntheticOpaque
  let mvar ← mkFreshExprMVar expectedType? kind
  registerMVarErrorHoleInfo mvar.mvarId! stx
  pure mvar

@[builtin_term_elab «syntheticHole»] def elabSyntheticHole : TermElab := fun stx expectedType? => do
  let arg  := stx[1]
  let userName := if arg.isIdent then arg.getId else Name.anonymous
  let mkNewHole : Unit → TermElabM Expr := fun _ => do
    let kind := if (← read).inPattern then MetavarKind.natural else MetavarKind.syntheticOpaque
    let mvar ← mkFreshExprMVar expectedType? kind userName
    registerMVarErrorHoleInfo mvar.mvarId! stx
    return mvar
  if userName.isAnonymous || (← read).inPattern then
    mkNewHole ()
  else
    match (← getMCtx).findUserName? userName with
    | none => mkNewHole ()
    | some mvarId =>
      let mvar := mkMVar mvarId
      let mvarDecl ← getMVarDecl mvarId
      let lctx ← getLCtx
      if mvarDecl.lctx.isSubPrefixOf lctx then
        return mvar
      else match (← getExprMVarAssignment? mvarId) with
      | some val =>
        let val ← instantiateMVars val
        if (← MetavarContext.isWellFormed lctx val) then
          return val
        else
          withLCtx mvarDecl.lctx mvarDecl.localInstances do
            throwError "synthetic hole has already been defined and assigned to value incompatible with the current context{indentExpr val}"
      | none =>
        if (← mvarId.isDelayedAssigned) then
          -- We can try to improve this case if needed.
          throwError "synthetic hole has already beend defined and delayed assigned with an incompatible local context"
        else if lctx.isSubPrefixOf mvarDecl.lctx then
          let mvarNew ← mkNewHole ()
          mvarId.assign mvarNew
          return mvarNew
        else
          throwError "synthetic hole has already been defined with an incompatible local context"

@[builtin_term_elab Lean.Parser.Term.omission] def elabOmission : TermElab := fun stx expectedType? => do
  logWarning m!"\
    The '⋯' token is used by the pretty printer to indicate omitted terms, and it should not be used directly. \
    It logs this warning and then elaborates like '_'.\
    \n\n\
    The presence of '⋯' in pretty printing output is controlled by the 'pp.maxSteps', 'pp.deepTerms' and 'pp.proofs' options. \
    These options can be further adjusted using 'pp.deepTerms.threshold' and 'pp.proofs.threshold'. \
    If this '⋯' was copied from the Infoview, the hover there for the original '⋯' explains which of these options led to the omission."
  elabHole stx expectedType?

@[builtin_term_elab «letMVar»] def elabLetMVar : TermElab := fun stx expectedType? => do
  match stx with
  | `(let_mvar% ? $n := $e; $b) =>
     match (← getMCtx).findUserName? n.getId with
     | some _ => throwError "invalid 'let_mvar%', metavariable '?{n.getId}' has already been used"
     | none =>
       let e ← elabTerm e none
       let mvar ← mkFreshExprMVar (← inferType e) MetavarKind.syntheticOpaque n.getId
       mvar.mvarId!.assign e
       -- We use `mkSaveInfoAnnotation` to make sure the info trees for `e` are saved even if `b` is a metavariable.
       return mkSaveInfoAnnotation (← elabTerm b expectedType?)
  | _ => throwUnsupportedSyntax

private def getMVarFromUserName (ident : Syntax) : MetaM Expr := do
  match (← getMCtx).findUserName? ident.getId with
  | none => throwError "unknown metavariable '?{ident.getId}'"
  | some mvarId => instantiateMVars (mkMVar mvarId)


@[builtin_term_elab «waitIfTypeMVar»] def elabWaitIfTypeMVar : TermElab := fun stx expectedType? => do
  match stx with
  | `(wait_if_type_mvar% ? $n; $b) =>
    tryPostponeIfMVar (← inferType (← getMVarFromUserName n))
    elabTerm b expectedType?
  | _ => throwUnsupportedSyntax

@[builtin_term_elab «waitIfTypeContainsMVar»] def elabWaitIfTypeContainsMVar : TermElab := fun stx expectedType? => do
  match stx with
  | `(wait_if_type_contains_mvar% ? $n; $b) =>
    if (← instantiateMVars (← inferType (← getMVarFromUserName n))).hasExprMVar then
      tryPostpone
    elabTerm b expectedType?
  | _ => throwUnsupportedSyntax

@[builtin_term_elab «waitIfContainsMVar»] def elabWaitIfContainsMVar : TermElab := fun stx expectedType? => do
  match stx with
  | `(wait_if_contains_mvar% ? $n; $b) =>
    if (← getMVarFromUserName n).hasExprMVar then
      tryPostpone
    elabTerm b expectedType?
  | _ => throwUnsupportedSyntax

@[builtin_term_elab byTactic] def elabByTactic : TermElab := fun stx expectedType? => do
  match expectedType? with
  | some expectedType =>
    mkTacticMVar expectedType stx .term
  | none =>
    tryPostpone
    throwError ("invalid 'by' tactic, expected type has not been provided")

@[builtin_term_elab noImplicitLambda] def elabNoImplicitLambda : TermElab := fun stx expectedType? =>
  elabTerm stx[1] (mkNoImplicitLambdaAnnotation <$> expectedType?)

@[builtin_term_elab Lean.Parser.Term.cdot] def elabBadCDot : TermElab := fun stx expectedType? => do
  if stx[0].getAtomVal == "." then
    -- Users may input bad cdots because they are trying to auto-complete them using the expected type
    addCompletionInfo <| CompletionInfo.dotId stx .anonymous (← getLCtx) expectedType?
  throwError "invalid occurrence of `·` notation, it must be surrounded by parentheses (e.g. `(· + 1)`)"

@[builtin_term_elab str] def elabStrLit : TermElab := fun stx _ => do
  match stx.isStrLit? with
  | some val => pure $ mkStrLit val
  | none     => throwIllFormedSyntax

private def mkFreshTypeMVarFor (expectedType? : Option Expr) : TermElabM Expr := do
  let typeMVar ← mkFreshTypeMVar MetavarKind.synthetic
  match expectedType? with
  | some expectedType => discard <| isDefEq expectedType typeMVar
  | _                 => pure ()
  return typeMVar

@[builtin_term_elab num] def elabNumLit : TermElab := fun stx expectedType? => do
  let val ← match stx.isNatLit? with
    | some val => pure val
    | none     => throwIllFormedSyntax
  let typeMVar ← mkFreshTypeMVarFor expectedType?
  let u ← try
    getDecLevel typeMVar
  catch ex =>
    match expectedType? with
    | some expectedType =>
      if (← isProp expectedType) then
        throwError m!"numerals are data in Lean, but the expected type is a proposition{indentExpr expectedType} : Prop"
      else
        throwError m!"numerals are data in Lean, but the expected type is universe polymorphic and may be a proposition{indentExpr expectedType} : {← inferType expectedType}"
    | none => throw ex
  let extraMsg := m!"numerals are polymorphic in Lean, but the numeral `{val}` cannot be used in a context where the expected type is{indentExpr typeMVar}\ndue to the absence of the instance above"
  let mvar ← mkInstMVar (mkApp2 (Lean.mkConst ``OfNat [u]) typeMVar (mkRawNatLit val)) extraMsg
  let r := mkApp3 (Lean.mkConst ``OfNat.ofNat [u]) typeMVar (mkRawNatLit val) mvar
  registerMVarErrorImplicitArgInfo mvar.mvarId! stx r
  return r

@[builtin_term_elab rawNatLit] def elabRawNatLit : TermElab :=  fun stx _ => do
  match stx[1].isNatLit? with
  | some val => return mkRawNatLit val
  | none     => throwIllFormedSyntax

@[builtin_term_elab scientific]
def elabScientificLit : TermElab := fun stx expectedType? => do
  match stx.isScientificLit? with
  | none        => throwIllFormedSyntax
  | some (m, sign, e) =>
    let typeMVar ← mkFreshTypeMVarFor expectedType?
    let u ← getDecLevel typeMVar
    let mvar ← mkInstMVar (mkApp (Lean.mkConst ``OfScientific [u]) typeMVar)
    let r := mkApp5 (Lean.mkConst ``OfScientific.ofScientific [u]) typeMVar mvar (mkRawNatLit m) (toExpr sign) (mkRawNatLit e)
    registerMVarErrorImplicitArgInfo mvar.mvarId! stx r
    return r

@[builtin_term_elab char] def elabCharLit : TermElab := fun stx _ => do
  match stx.isCharLit? with
  | some val => return mkApp (Lean.mkConst ``Char.ofNat) (mkRawNatLit val.toNat)
  | none     => throwIllFormedSyntax

@[builtin_term_elab quotedName] def elabQuotedName : TermElab := fun stx _ =>
  match stx[0].isNameLit? with
  | some val => pure $ toExpr val
  | none     => throwIllFormedSyntax

@[builtin_term_elab doubleQuotedName] def elabDoubleQuotedName : TermElab := fun stx _ =>
  return toExpr (← realizeGlobalConstNoOverloadWithInfo stx[2])

@[builtin_term_elab declName] def elabDeclName : TermElab := adaptExpander fun _ => do
  let some declName ← getDeclName?
    | throwError "invalid `decl_name%` macro, the declaration name is not available"
  return (quote declName : Term)

@[builtin_term_elab Parser.Term.withDeclName] def elabWithDeclName : TermElab := fun stx expectedType? => do
  let id := stx[2].getId
  let id ← if stx[1].isNone then pure id else pure <| (← getCurrNamespace) ++ id
  let e := stx[3]
  withMacroExpansion stx e <| withDeclName id <| elabTerm e expectedType?

@[builtin_term_elab typeOf] def elabTypeOf : TermElab := fun stx _ => do
  inferType (← elabTerm stx[1] none)

/--
  Recall that `mkTermInfo` does not create an `ofTermInfo` node in the info tree
  if `e` corresponds to a hole that is going to be filled "later" by executing a tactic or resuming elaboration.
  This behavior is problematic for auxiliary elaboration steps that are "almost" no-ops.
  For example, consider the elaborator for
  ```
  ensure_type_of% s msg e
  ```
  It elaborates `s`, infers its type `t`, and then elaborates `e` ensuring the resulting type is `t`.
  If the elaboration of `e` is postponed, then the result is just a metavariable, and an `ofTermInfo` would not be created.
  This happens because `ensure_type_of%` is almost a no-op. The elaboration of `s` does not directly contribute to the
  final result, just its type.
  To make sure, we don't miss any information in the `InfoTree`, we can just create a "silent" annotation to force
  `mTermInfo` to create a node for the `ensure_type_of% s msg e` even if `e` has been postponed.

  Another possible solution is to elaborate `ensure_type_of% s msg e` as `ensureType s e` where `ensureType` has type
  ```
  ensureType (s e : α) := e
  ```
  We decided to use the silent notation because `ensure_type_of%` is heavily used in the `Do` elaborator, and the extra
  overhead could be significant.
-/
private def mkSilentAnnotationIfHole (e : Expr) : TermElabM Expr := do
  if (← isTacticOrPostponedHole? e).isSome then
    return mkAnnotation `_silent e
  else
    return e

@[builtin_term_elab ensureTypeOf] def elabEnsureTypeOf : TermElab := fun stx _ =>
  match stx[2].isStrLit? with
  | none     => throwIllFormedSyntax
  | some msg => do
    let refTerm ← elabTerm stx[1] none
    let refTermType ← inferType refTerm
    -- See comment at `mkSilentAnnotationIfHole`
    mkSilentAnnotationIfHole (← elabTermEnsuringType stx[3] refTermType (errorMsgHeader? := msg))

@[builtin_term_elab ensureExpectedType] def elabEnsureExpectedType : TermElab := fun stx expectedType? =>
  match stx[1].isStrLit? with
  | none     => throwIllFormedSyntax
  | some msg => elabTermEnsuringType stx[2] expectedType? (errorMsgHeader? := msg)

@[builtin_term_elab clear] def elabClear : TermElab := fun stx expectedType? => do
  let some (.fvar fvarId) ← isLocalIdent? stx[1]
    | throwErrorAt stx[1] "not in scope"
  let body := stx[3]
  let canClear ← id do
    if let some expectedType := expectedType? then
      if ← dependsOn expectedType fvarId then
        return false
    for ldecl in ← getLCtx do
      if ldecl.fvarId != fvarId then
        if ← localDeclDependsOn ldecl fvarId then
          return false
    return true
  if canClear then
    withErasedFVars #[fvarId] do elabTerm body expectedType?
  else
    elabTerm body expectedType?

@[builtin_term_elab «open»] def elabOpen : TermElab := fun stx expectedType? => do
  let `(open $decl in $e) := stx | throwUnsupportedSyntax
  try
    pushScope
    let openDecls ← elabOpenDecl decl
    withTheReader Core.Context (fun ctx => { ctx with openDecls := openDecls }) do
      elabTerm e expectedType?
  finally
    popScope

@[builtin_term_elab «set_option»] def elabSetOption : TermElab := fun stx expectedType? => do
  let options ← Elab.elabSetOption stx[1] stx[3]
  withOptions (fun _ => options) do
    try
      elabTerm stx[5] expectedType?
    finally
      if stx[1].getId == `diagnostics then
        reportDiag

@[builtin_term_elab withAnnotateTerm] def elabWithAnnotateTerm : TermElab := fun stx expectedType? => do
  match stx with
  | `(with_annotate_term $stx $e) =>
    withInfoContext'
      stx
      (elabTerm e expectedType?)
      (mkTermInfo .anonymous (expectedType? := expectedType?) stx)
      (mkPartialTermInfo .anonymous (expectedType? := expectedType?) stx)
  | _ => throwUnsupportedSyntax

private unsafe def evalFilePathUnsafe (stx : Syntax) : TermElabM System.FilePath :=
  evalTerm System.FilePath (Lean.mkConst ``System.FilePath) stx

@[implemented_by evalFilePathUnsafe]
private opaque evalFilePath (stx : Syntax) : TermElabM System.FilePath

@[builtin_term_elab includeStr] def elabIncludeStr : TermElab
  | `(include_str $path:term), _ => do
    let path ← evalFilePath path
    let ctx ← readThe Lean.Core.Context
    let srcPath := System.FilePath.mk ctx.fileName
    let some srcDir := srcPath.parent
      | throwError "cannot compute parent directory of '{srcPath}'"
    let path := srcDir / path
    mkStrLit <$> IO.FS.readFile path
  | _, _ => throwUnsupportedSyntax

@[builtin_term_elab Lean.Parser.Term.namedPattern] def elabNamedPatternErr : TermElab := fun stx _ =>
  throwError "`<identifier>@<term>` is a named pattern and can only be used in pattern matching contexts{indentD stx}"

end Lean.Elab.Term
