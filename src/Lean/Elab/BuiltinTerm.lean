/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Term

namespace Lean.Elab.Term
open Meta

/-- The universe of propositions. `Prop ≡ Sort 0`. -/
@[builtinTermElab «prop»] def elabProp : TermElab := fun _ _ =>
  return mkSort levelZero

private def elabOptLevel (stx : Syntax) : TermElabM Level :=
  if stx.isNone then
    pure levelZero
  else
    elabLevel stx[0]

/-- A specific universe in Lean's infinite hierarchy of universes. -/
@[builtinTermElab «sort»] def elabSort : TermElab := fun stx _ =>
  return mkSort (← elabOptLevel stx[1])

/-- A type universe. `Type ≡ Type 0`, `Type u ≡ Sort (u + 1)`. -/
@[builtinTermElab «type»] def elabTypeStx : TermElab := fun stx _ =>
  return mkSort (mkLevelSucc (← elabOptLevel stx[1]))

/-!
 the method `resolveName` adds a completion point for it using the given
    expected type. Thus, we propagate the expected type if `stx[0]` is an identifier.
    It doesn't "hurt" if the identifier can be resolved because the expected type is not used in this case.
    Recall that if the name resolution fails a synthetic sorry is returned.-/

@[builtinTermElab «pipeCompletion»] def elabPipeCompletion : TermElab := fun stx expectedType? => do
  let e ← elabTerm stx[0] none
  unless e.isSorry do
    addDotCompletionInfo stx e expectedType?
  throwErrorAt stx[1] "invalid field notation, identifier or numeral expected"

@[builtinTermElab «completion»] def elabCompletion : TermElab := fun stx expectedType? => do
  /- `ident.` is ambiguous in Lean, we may try to be completing a declaration name or access a "field". -/
  if stx[0].isIdent then
    /- If we can elaborate the identifier successfully, we assume it is a dot-completion. Otherwise, we treat it as
       identifier completion with a dangling `.`.
       Recall that the server falls back to identifier completion when dot-completion fails. -/
    let s ← saveState
    try
      let e ← elabTerm stx[0] none
      addDotCompletionInfo stx e expectedType?
    catch _ =>
      s.restore
      addCompletionInfo <| CompletionInfo.id stx stx[0].getId (danglingDot := true) (← getLCtx) expectedType?
    throwErrorAt stx[1] "invalid field notation, identifier or numeral expected"
  else
    elabPipeCompletion stx expectedType?

/-- A placeholder term, to be synthesized by unification. -/
@[builtinTermElab «hole»] def elabHole : TermElab := fun stx expectedType? => do
  let mvar ← mkFreshExprMVar expectedType?
  registerMVarErrorHoleInfo mvar.mvarId! stx
  pure mvar

@[builtinTermElab «syntheticHole»] def elabSyntheticHole : TermElab := fun stx expectedType? => do
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

@[builtinTermElab «letMVar»] def elabLetMVar : TermElab := fun stx expectedType? => do
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


@[builtinTermElab «waitIfTypeMVar»] def elabWaitIfTypeMVar : TermElab := fun stx expectedType? => do
  match stx with
  | `(wait_if_type_mvar% ? $n; $b) =>
    tryPostponeIfMVar (← inferType (← getMVarFromUserName n))
    elabTerm b expectedType?
  | _ => throwUnsupportedSyntax

@[builtinTermElab «waitIfTypeContainsMVar»] def elabWaitIfTypeContainsMVar : TermElab := fun stx expectedType? => do
  match stx with
  | `(wait_if_type_contains_mvar% ? $n; $b) =>
    if (← instantiateMVars (← inferType (← getMVarFromUserName n))).hasExprMVar then
      tryPostpone
    elabTerm b expectedType?
  | _ => throwUnsupportedSyntax

@[builtinTermElab «waitIfContainsMVar»] def elabWaitIfContainsMVar : TermElab := fun stx expectedType? => do
  match stx with
  | `(wait_if_contains_mvar% ? $n; $b) =>
    if (← getMVarFromUserName n).hasExprMVar then
      tryPostpone
    elabTerm b expectedType?
  | _ => throwUnsupportedSyntax

private def mkTacticMVar (type : Expr) (tacticCode : Syntax) : TermElabM Expr := do
  let mvar ← mkFreshExprMVar type MetavarKind.syntheticOpaque
  let mvarId := mvar.mvarId!
  let ref ← getRef
  registerSyntheticMVar ref mvarId <| SyntheticMVarKind.tactic tacticCode (← saveContext)
  return mvar

/-- `by tac` constructs a term of the expected type by running the tactic(s) `tac`. -/
@[builtinTermElab byTactic] def elabByTactic : TermElab := fun stx expectedType? => do
  tryPostponeIfNoneOrMVar expectedType?
  match expectedType? with
  | some expectedType => mkTacticMVar expectedType stx
  | none => throwError ("invalid 'by' tactic, expected type has not been provided")

@[builtinTermElab noImplicitLambda] def elabNoImplicitLambda : TermElab := fun stx expectedType? =>
  elabTerm stx[1] (mkNoImplicitLambdaAnnotation <$> expectedType?)

@[builtinTermElab cdot] def elabBadCDot : TermElab := fun _ _ =>
  throwError "invalid occurrence of `·` notation, it must be surrounded by parentheses (e.g. `(· + 1)`)"

@[builtinTermElab str] def elabStrLit : TermElab := fun stx _ => do
  match stx.isStrLit? with
  | some val => pure $ mkStrLit val
  | none     => throwIllFormedSyntax

private def mkFreshTypeMVarFor (expectedType? : Option Expr) : TermElabM Expr := do
  let typeMVar ← mkFreshTypeMVar MetavarKind.synthetic
  match expectedType? with
  | some expectedType => discard <| isDefEq expectedType typeMVar
  | _                 => pure ()
  return typeMVar

@[builtinTermElab num] def elabNumLit : TermElab := fun stx expectedType? => do
  let val ← match stx.isNatLit? with
    | some val => pure val
    | none     => throwIllFormedSyntax
  let typeMVar ← mkFreshTypeMVarFor expectedType?
  let u ← getDecLevel typeMVar
  let mvar ← mkInstMVar (mkApp2 (Lean.mkConst ``OfNat [u]) typeMVar (mkRawNatLit val))
  let r := mkApp3 (Lean.mkConst ``OfNat.ofNat [u]) typeMVar (mkRawNatLit val) mvar
  registerMVarErrorImplicitArgInfo mvar.mvarId! stx r
  return r

@[builtinTermElab rawNatLit] def elabRawNatLit : TermElab :=  fun stx _ => do
  match stx[1].isNatLit? with
  | some val => return mkRawNatLit val
  | none     => throwIllFormedSyntax

@[builtinTermElab scientific]
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

@[builtinTermElab char] def elabCharLit : TermElab := fun stx _ => do
  match stx.isCharLit? with
  | some val => return mkApp (Lean.mkConst ``Char.ofNat) (mkRawNatLit val.toNat)
  | none     => throwIllFormedSyntax

/-- A literal of type `Name`. -/
@[builtinTermElab quotedName] def elabQuotedName : TermElab := fun stx _ =>
  match stx[0].isNameLit? with
  | some val => pure $ toExpr val
  | none     => throwIllFormedSyntax

/--
A resolved name literal. Evaluates to the full name of the given constant if
existent in the current context, or else fails. -/
@[builtinTermElab doubleQuotedName] def elabDoubleQuotedName : TermElab := fun stx _ =>
  return toExpr (← resolveGlobalConstNoOverloadWithInfo stx[2])

@[builtinTermElab typeOf] def elabTypeOf : TermElab := fun stx _ => do
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

@[builtinTermElab ensureTypeOf] def elabEnsureTypeOf : TermElab := fun stx _ =>
  match stx[2].isStrLit? with
  | none     => throwIllFormedSyntax
  | some msg => do
    let refTerm ← elabTerm stx[1] none
    let refTermType ← inferType refTerm
    -- See comment at `mkSilentAnnotationIfHole`
    mkSilentAnnotationIfHole (← elabTermEnsuringType stx[3] refTermType (errorMsgHeader? := msg))

@[builtinTermElab ensureExpectedType] def elabEnsureExpectedType : TermElab := fun stx expectedType? =>
  match stx[1].isStrLit? with
  | none     => throwIllFormedSyntax
  | some msg => elabTermEnsuringType stx[2] expectedType? (errorMsgHeader? := msg)

/-- `open ... in e` makes the given namespaces available in the term `e`. -/
@[builtinTermElab «open»] def elabOpen : TermElab := fun stx expectedType? => do
  try
    pushScope
    let openDecls ← elabOpenDecl stx[1]
    withTheReader Core.Context (fun ctx => { ctx with openDecls := openDecls }) do
      elabTerm stx[3] expectedType?
  finally
    popScope

/-- `set_option opt val in e` sets the option `opt` to the value `val` in the term `e`. -/
@[builtinTermElab «set_option»] def elabSetOption : TermElab := fun stx expectedType? => do
  let options ← Elab.elabSetOption stx[1] stx[2]
  withTheReader Core.Context (fun ctx => { ctx with maxRecDepth := maxRecDepth.get options, options := options }) do
    elabTerm stx[4] expectedType?

@[builtinTermElab withAnnotateTerm] def elabWithAnnotateTerm : TermElab := fun stx expectedType? => do
  match stx with
  | `(with_annotate_term $stx $e) =>
    withInfoContext' stx (elabTerm e expectedType?) (mkTermInfo .anonymous (expectedType? := expectedType?) stx)
  | _ => throwUnsupportedSyntax

end Lean.Elab.Term
