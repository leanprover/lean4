/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Attributes
import Lean.Elab.Binders
import Lean.Elab.DeclModifiers
import Lean.Elab.SyntheticMVars
import Lean.Elab.DeclarationRange

namespace Lean.Elab.Term
open Meta

structure LetRecDeclView where
  ref           : Syntax
  attrs         : Array Attribute
  shortDeclName : Name
  declName      : Name
  numParams     : Nat
  type          : Expr
  mvar          : Expr -- auxiliary metavariable used to lift the 'let rec'
  valStx        : Syntax

structure LetRecView where
  decls     : Array LetRecDeclView
  body      : Syntax

/-  group ("let " >> nonReservedSymbol "rec ") >> sepBy1 (group (optional «attributes» >> letDecl)) ", " >> "; " >> termParser -/
private def mkLetRecDeclView (letRec : Syntax) : TermElabM LetRecView := do
  let decls ← letRec[1][0].getSepArgs.mapM fun (attrDeclStx : Syntax) => do
    let docStr? ← expandOptDocComment? attrDeclStx[0]
    let attrOptStx := attrDeclStx[1]
    let attrs ← if attrOptStx.isNone then pure #[] else elabDeclAttrs attrOptStx[0]
    let decl := attrDeclStx[2][0]
    if decl.isOfKind `Lean.Parser.Term.letPatDecl then
      throwErrorAt decl "patterns are not allowed in 'let rec' expressions"
    else if decl.isOfKind `Lean.Parser.Term.letIdDecl || decl.isOfKind `Lean.Parser.Term.letEqnsDecl then
      let declId := decl[0]
      let shortDeclName := declId.getId
      let currDeclName? ← getDeclName?
      let declName := currDeclName?.getD Name.anonymous ++ shortDeclName
      checkNotAlreadyDeclared declName
      applyAttributesAt declName attrs AttributeApplicationTime.beforeElaboration
      addDocString' declName docStr?
      addAuxDeclarationRanges declName decl declId
      let binders := decl[1].getArgs
      let typeStx := expandOptType declId decl[2]
      let (type, numParams) ← elabBinders binders fun xs => do
          let type ← elabType typeStx
          registerCustomErrorIfMVar type typeStx "failed to infer 'let rec' declaration type"
          let type ← mkForallFVars xs type
          pure (type, xs.size)
      let mvar ← mkFreshExprMVar type MetavarKind.syntheticOpaque
      let valStx ←
        if decl.isOfKind `Lean.Parser.Term.letIdDecl then
          pure decl[4]
        else
          liftMacroM $ expandMatchAltsIntoMatch decl decl[3]
      pure {
        ref           := decl,
        attrs         := attrs,
        shortDeclName := shortDeclName,
        declName      := declName,
        numParams     := numParams,
        type          := type,
        mvar          := mvar,
        valStx        := valStx
        : LetRecDeclView }
    else
      throwUnsupportedSyntax
  pure {
    decls := decls,
    body  := letRec[3]
  }

private partial def withAuxLocalDecls {α} (views : Array LetRecDeclView) (k : Array Expr → TermElabM α) : TermElabM α :=
  let rec loop (i : Nat) (fvars : Array Expr) : TermElabM α :=
    if h : i < views.size then
      let view := views.get ⟨i, h⟩
      withLocalDeclD view.shortDeclName view.type fun fvar => loop (i+1) (fvars.push fvar)
    else
      k fvars
  loop 0 #[]

private def elabLetRecDeclValues (view : LetRecView) : TermElabM (Array Expr) :=
  view.decls.mapM fun view => do
    forallBoundedTelescope view.type view.numParams fun xs type =>
       withDeclName view.declName do
         let value ← elabTermEnsuringType view.valStx type
         mkLambdaFVars xs value

private def registerLetRecsToLift (views : Array LetRecDeclView) (fvars : Array Expr) (values : Array Expr) : TermElabM Unit := do
  let letRecsToLiftCurr := (← get).letRecsToLift
  for view in views do
    if letRecsToLiftCurr.any fun toLift => toLift.declName == view.declName then
      withRef view.ref do
        throwError "'{view.declName}' has already been declared"
  let lctx ← getLCtx
  let localInsts ← getLocalInstances
  let toLift := views.mapIdx fun i view => {
    ref            := view.ref,
    fvarId         := fvars[i].fvarId!,
    attrs          := view.attrs,
    shortDeclName  := view.shortDeclName,
    declName       := view.declName,
    lctx           := lctx,
    localInstances := localInsts,
    type           := view.type,
    val            := values[i],
    mvarId         := view.mvar.mvarId!
    : LetRecToLift }
  modify fun s => { s with letRecsToLift := toLift.toList ++ s.letRecsToLift }

@[builtinTermElab «letrec»] def elabLetRec : TermElab := fun stx expectedType? => do
  let view ← mkLetRecDeclView stx
  withAuxLocalDecls view.decls fun fvars => do
    for decl in view.decls, fvar in fvars do
      addTermInfo (isBinder := true) decl.ref[0] fvar
    let values ← elabLetRecDeclValues view
    let body ← elabTermEnsuringType view.body expectedType?
    registerLetRecsToLift view.decls fvars values
    let mvars := view.decls.map (·.mvar)
    pure $ mkAppN (← mkLambdaFVars fvars body) mvars

end Lean.Elab.Term
