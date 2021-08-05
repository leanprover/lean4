/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Term

namespace Lean.Elab.Term
open Meta

@[builtinTermElab «prop»] def elabProp : TermElab := fun _ _ =>
  return mkSort levelZero

private def elabOptLevel (stx : Syntax) : TermElabM Level :=
  if stx.isNone then
    pure levelZero
  else
    elabLevel stx[0]

@[builtinTermElab «sort»] def elabSort : TermElab := fun stx _ =>
  return mkSort (← elabOptLevel stx[1])

@[builtinTermElab «type»] def elabTypeStx : TermElab := fun stx _ =>
  return mkSort (mkLevelSucc (← elabOptLevel stx[1]))

/-
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
    /- If we can elaborate the identifier successfully, we assume it a dot-completion. Otherwise, we treat it as
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

@[builtinTermElab «hole»] def elabHole : TermElab := fun stx expectedType? => do
  let mvar ← mkFreshExprMVar expectedType?
  registerMVarErrorHoleInfo mvar.mvarId! stx
  pure mvar

@[builtinTermElab «syntheticHole»] def elabSyntheticHole : TermElab := fun stx expectedType? => do
  let arg  := stx[1]
  let userName := if arg.isIdent then arg.getId else Name.anonymous
  let mkNewHole : Unit → TermElabM Expr := fun _ => do
    let mvar ← mkFreshExprMVar expectedType? MetavarKind.syntheticOpaque userName
    registerMVarErrorHoleInfo mvar.mvarId! stx
    pure mvar
  if userName.isAnonymous then
    mkNewHole ()
  else
    let mctx ← getMCtx
    match mctx.findUserName? userName with
    | none => mkNewHole ()
    | some mvarId =>
      let mvar := mkMVar mvarId
      let mvarDecl ← getMVarDecl mvarId
      let lctx ← getLCtx
      if mvarDecl.lctx.isSubPrefixOf lctx then
        pure mvar
      else match mctx.getExprAssignment? mvarId with
      | some val =>
        let val ← instantiateMVars val
        if mctx.isWellFormed lctx val then
          pure val
        else
          withLCtx mvarDecl.lctx mvarDecl.localInstances do
            throwError "synthetic hole has already been defined and assigned to value incompatible with the current context{indentExpr val}"
      | none =>
        if mctx.isDelayedAssigned mvarId then
          -- We can try to improve this case if needed.
          throwError "synthetic hole has already beend defined and delayed assigned with an incompatible local context"
        else if lctx.isSubPrefixOf mvarDecl.lctx then
          let mvarNew ← mkNewHole ()
          modifyMCtx fun mctx => mctx.assignExpr mvarId mvarNew
          pure mvarNew
        else
          throwError "synthetic hole has already been defined with an incompatible local context"

private def mkTacticMVar (type : Expr) (tacticCode : Syntax) : TermElabM Expr := do
  let mvar ← mkFreshExprMVar type MetavarKind.syntheticOpaque
  let mvarId := mvar.mvarId!
  let ref ← getRef
  let declName? ← getDeclName?
  registerSyntheticMVar ref mvarId <| SyntheticMVarKind.tactic tacticCode (← saveContext)
  return mvar

@[builtinTermElab byTactic] def elabByTactic : TermElab := fun stx expectedType? =>
  match expectedType? with
  | some expectedType => mkTacticMVar expectedType stx
  | none => throwError ("invalid 'by' tactic, expected type has not been provided")

@[builtinTermElab noImplicitLambda] def elabNoImplicitLambda : TermElab := fun stx expectedType? =>
  elabTerm stx[1] (mkNoImplicitLambdaAnnotation <$> expectedType?)

@[builtinTermElab cdot] def elabBadCDot : TermElab := fun stx _ =>
  throwError "invalid occurrence of `·` notation, it must be surrounded by parentheses (e.g. `(· + 1)`)"

@[builtinTermElab strLit] def elabStrLit : TermElab := fun stx _ => do
  match stx.isStrLit? with
  | some val => pure $ mkStrLit val
  | none     => throwIllFormedSyntax

private def mkFreshTypeMVarFor (expectedType? : Option Expr) : TermElabM Expr := do
  let typeMVar ← mkFreshTypeMVar MetavarKind.synthetic
  match expectedType? with
  | some expectedType => discard <| isDefEq expectedType typeMVar
  | _                 => pure ()
  return typeMVar

@[builtinTermElab numLit] def elabNumLit : TermElab := fun stx expectedType? => do
  let val ← match stx.isNatLit? with
    | some val => pure val
    | none     => throwIllFormedSyntax
  let typeMVar ← mkFreshTypeMVarFor expectedType?
  let u ← getDecLevel typeMVar
  let mvar ← mkInstMVar (mkApp2 (Lean.mkConst ``OfNat [u]) typeMVar (mkRawNatLit val))
  let r := mkApp3 (Lean.mkConst ``OfNat.ofNat [u]) typeMVar (mkRawNatLit val) mvar
  registerMVarErrorImplicitArgInfo mvar.mvarId! stx r
  return r

@[builtinTermElab rawNatLit] def elabRawNatLit : TermElab :=  fun stx expectedType? => do
  match stx[1].isNatLit? with
  | some val => return mkRawNatLit val
  | none     => throwIllFormedSyntax

@[builtinTermElab scientificLit]
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

@[builtinTermElab charLit] def elabCharLit : TermElab := fun stx _ => do
  match stx.isCharLit? with
  | some val => return mkApp (Lean.mkConst ``Char.ofNat) (mkRawNatLit val.toNat)
  | none     => throwIllFormedSyntax

@[builtinTermElab quotedName] def elabQuotedName : TermElab := fun stx _ =>
  match stx[0].isNameLit? with
  | some val => pure $ toExpr val
  | none     => throwIllFormedSyntax

@[builtinTermElab doubleQuotedName] def elabDoubleQuotedName : TermElab := fun stx _ => do
  toExpr (← resolveGlobalConstNoOverloadWithInfo stx[2])

@[builtinTermElab typeOf] def elabTypeOf : TermElab := fun stx _ => do
  inferType (← elabTerm stx[1] none)

@[builtinTermElab ensureTypeOf] def elabEnsureTypeOf : TermElab := fun stx expectedType? =>
  match stx[2].isStrLit? with
  | none     => throwIllFormedSyntax
  | some msg => do
    let refTerm ← elabTerm stx[1] none
    let refTermType ← inferType refTerm
    elabTermEnsuringType stx[3] refTermType (errorMsgHeader? := msg)

@[builtinTermElab ensureExpectedType] def elabEnsureExpectedType : TermElab := fun stx expectedType? =>
  match stx[1].isStrLit? with
  | none     => throwIllFormedSyntax
  | some msg => elabTermEnsuringType stx[2] expectedType? (errorMsgHeader? := msg)

@[builtinTermElab «open»] def elabOpen : TermElab := fun stx expectedType? => do
  try
    pushScope
    let openDecls ← elabOpenDecl stx[1]
    withTheReader Core.Context (fun ctx => { ctx with openDecls := openDecls }) do
      elabTerm stx[3] expectedType?
  finally
    popScope

@[builtinTermElab «set_option»] def elabSetOption : TermElab := fun stx expectedType? => do
  let options ← Elab.elabSetOption stx[1] stx[2]
  withTheReader Core.Context (fun ctx => { ctx with maxRecDepth := maxRecDepth.get options, options := options }) do
    elabTerm stx[4] expectedType?

end Lean.Elab.Term
