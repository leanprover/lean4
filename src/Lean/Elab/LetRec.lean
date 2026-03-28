/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Elab.MutualDef

public section

namespace Lean.Elab.Term
open Meta

structure LetRecDeclView where
  ref           : Syntax
  attrs         : Array Attribute
  shortDeclName : Name
  declName      : Name
  parentName?   : Option Name
  binderIds     : Array Syntax
  binders       : Syntax -- binder syntax for docstring elaboration
  type          : Expr
  mvar          : Expr -- auxiliary metavariable used to lift the 'let rec'
  valStx        : Syntax
  termination   : TerminationHints
  docString?    : Option (TSyntax ``Parser.Command.docComment × Bool) := none

structure LetRecView where
  decls     : Array LetRecDeclView
  body      : Syntax

/-  group ("let " >> nonReservedSymbol "rec ") >> sepBy1 (group (optional «attributes» >> letDecl)) ", " >> "; " >> termParser -/
private def mkLetRecDeclView (letRec : Syntax) : TermElabM LetRecView := do
  let mut decls : Array LetRecDeclView := #[]
  let isVerso := doc.verso.get (← getOptions)
  for attrDeclStx in letRec[1][0].getSepArgs do
    let docStr? := attrDeclStx[0].getOptional?.map (TSyntax.mk ·, isVerso)
    let attrOptStx := attrDeclStx[1]
    let attrs ← if attrOptStx.isNone then pure #[] else elabDeclAttrs attrOptStx[0]
    let decl := attrDeclStx[2][0]
    if decl.isOfKind `Lean.Parser.Term.letPatDecl then
      throwErrorAt decl "patterns are not allowed in 'let rec' expressions"
    else if decl.isOfKind ``Lean.Parser.Term.letIdDecl || decl.isOfKind ``Lean.Parser.Term.letEqnsDecl then
      let declId := decl[0][0]
      unless declId.isIdent do
        throwErrorAt declId "'let rec' expressions must be named"
      let shortDeclName := declId.getId
      let parentName? ← getDeclName?
      let mut declName := parentName?.getD Name.anonymous ++ shortDeclName
      let env ← getEnv
      if env.header.isModule && !env.isExporting then
        declName := mkPrivateName env declName
      if decls.any fun decl => decl.declName == declName then
        withRef declId do
          throwError "`{.ofConstName declName}` has already been declared"
      let binderStx := decl[1]
      checkNotAlreadyDeclared declName
      applyAttributesAt declName attrs AttributeApplicationTime.beforeElaboration
      -- Docstring processing is deferred until the declaration is added to the environment.
      -- This is necessary for Verso docstrings to work correctly, as they may reference the
      -- declaration being defined.
      addDeclarationRangesFromSyntax declName decl declId
      let binders := binderStx.getArgs
      let typeStx := expandOptType declId decl[2]
      let (type, binderIds) ← elabBindersEx binders fun xs => do
          let type ← elabType typeStx
          registerCustomErrorIfMVar type typeStx "failed to infer 'let rec' declaration type"
          let (binderIds, xs) := xs.unzip
          let type ← mkForallFVars xs type
          pure (type, binderIds)
      let mvar ← mkFreshExprMVar type MetavarKind.syntheticOpaque
      let valStx ← if decl.isOfKind `Lean.Parser.Term.letIdDecl then
        pure decl[4]
      else
        liftMacroM <| expandMatchAltsIntoMatch decl decl[3]
      let termination ← elabTerminationHints ⟨attrDeclStx[3]⟩
      decls := decls.push {
        ref := declId, attrs, shortDeclName, declName, parentName?,
        binderIds, binders := binderStx, type, mvar, valStx, termination, docString? := docStr?
      }
    else
      throwUnsupportedSyntax
  return { decls, body := letRec[3] }

private partial def withAuxLocalDecls {α} (views : Array LetRecDeclView) (k : Array Expr → TermElabM α) : TermElabM α :=
  let rec loop (i : Nat) (fvars : Array Expr) : TermElabM α :=
    if h : i < views.size then
      let view := views[i]
      withAuxDecl view.shortDeclName view.type view.declName fun fvar => loop (i+1) (fvars.push fvar)
    else
      k fvars
  loop 0 #[]

private def elabLetRecDeclValues (view : LetRecView) : TermElabM (Array Expr) :=
  view.decls.mapM fun view => do
    forallBoundedTelescope view.type view.binderIds.size (cleanupAnnotations := true) fun xs type => do
      -- Add new info nodes for new fvars. The server will detect all fvars of a binder by the binder's source location.
      for h : i in *...view.binderIds.size do
        addLocalVarInfo view.binderIds[i] xs[i]!
      withDeclName view.declName do
        withInfoContext' view.valStx
          (mkInfo := (pure <| .inl <| mkBodyInfo view.valStx ·))
          (mkInfoOnError := (pure <| mkBodyInfo view.valStx none))
          do
            let value ← elabTermEnsuringType view.valStx type
            mkLambdaFVars xs value

private def registerLetRecsToLift (views : Array LetRecDeclView) (fvars : Array Expr) (values : Array Expr) : TermElabM Unit := do
  let letRecsToLiftCurr := (← get).letRecsToLift
  for view in views do
    if letRecsToLiftCurr.any fun toLift => toLift.declName == view.declName then
      withRef view.ref do
        throwError "`{view.declName}` has already been declared"
  let lctx ← getLCtx
  let localInstances ← getLocalInstances

  let toLift ← views.mapIdxM fun i view => do
    let value := values[i]!
    let termination := view.termination.rememberExtraParams view.binderIds.size value
    pure {
      ref            := view.ref
      fvarId         := fvars[i]!.fvarId!
      attrs          := view.attrs
      shortDeclName  := view.shortDeclName
      declName       := view.declName
      parentName?    := view.parentName?
      lctx
      localInstances
      type           := view.type
      val            := value
      mvarId         := view.mvar.mvarId!
      termination
      binders        := view.binders
      docString?     := view.docString?
    }
  modify fun s => { s with letRecsToLift := toLift.toList ++ s.letRecsToLift }

@[builtin_term_elab «letrec»] def elabLetRec : TermElab := fun stx expectedType? => do
  let view ← mkLetRecDeclView stx
  withAuxLocalDecls view.decls fun fvars => do
    for decl in view.decls, fvar in fvars do
      addLocalVarInfo decl.ref fvar
    let values ← elabLetRecDeclValues view
    let body ← elabTermEnsuringType view.body expectedType?
    registerLetRecsToLift view.decls fvars values
    let mvars := view.decls.map (·.mvar)
    return mkAppN (← mkLambdaFVars fvars body) mvars

end Lean.Elab.Term
