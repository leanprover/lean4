/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Attributes
import Lean.Elab.Binders
import Lean.Elab.DeclModifiers
import Lean.Elab.SyntheticMVars

namespace Lean
namespace Elab
namespace Term

open Meta

structure LetRecDeclView :=
(ref           : Syntax)
(attrs         : Array Attribute)
(shortDeclName : Name)
(declName      : Name)
(numParams     : Nat)
(type          : Expr)
(mvar          : Expr) -- auxiliary metavariable used to lift the 'let rec'
(valStx        : Syntax)

structure LetRecView :=
(decls     : Array LetRecDeclView)
(body      : Syntax)

/-  group ("let " >> nonReservedSymbol "rec ") >> sepBy1 (group (optional «attributes» >> letDecl)) ", " >> "; " >> termParser -/
private def mkLetRecDeclView (letRec : Syntax) : TermElabM LetRecView := do
decls ← (letRec.getArg 1).getArgs.getSepElems.mapM fun attrDeclStx => do {
  let attrStx := attrDeclStx.getArg 0;
  attrs ← elabAttrs attrStx;
  let decl    := (attrDeclStx.getArg 1).getArg 0;
  if decl.isOfKind `Lean.Parser.Term.letPatDecl then
    throwErrorAt decl "patterns are not allowed in 'let rec' expressions"
  else if decl.isOfKind `Lean.Parser.Term.letIdDecl || decl.isOfKind `Lean.Parser.Term.letEqnsDecl then do
    let shortDeclName := decl.getIdAt 0;
    currDeclName? ← getDeclName?;
    let declName := currDeclName?.getD Name.anonymous ++ shortDeclName;
    checkNotAlreadyDeclared declName;
    applyAttributes declName attrs AttributeApplicationTime.beforeElaboration;
    let binders := (decl.getArg 1).getArgs;
    let typeStx := expandOptType decl (decl.getArg 2);
    (type, numParams) ← elabBinders binders fun xs => do {
        type ← elabType typeStx;
        type ← mkForallFVars xs type;
        pure (type, xs.size)
    };
    mvar ← mkFreshExprMVar type MetavarKind.syntheticOpaque;
    valStx ←
      if decl.isOfKind `Lean.Parser.Term.letIdDecl then
        pure $ decl.getArg 4
      else
        liftMacroM $ expandMatchAltsIntoMatch decl (decl.getArg 4);
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
};
pure {
  decls := decls,
  body  := letRec.getArg 3
}

private partial def withAuxLocalDeclsAux {α} (views : Array LetRecDeclView) (k : Array Expr → TermElabM α) : Nat → Array Expr → TermElabM α
| i, fvars =>
  if h : i < views.size then
    let view := views.get ⟨i, h⟩;
    withLetDecl view.shortDeclName view.type view.mvar fun fvar => withAuxLocalDeclsAux (i+1) (fvars.push fvar)
  else
    k fvars

private def withAuxLocalDecls {α} (views : Array LetRecDeclView) (k : Array Expr → TermElabM α) : TermElabM α :=
withAuxLocalDeclsAux views k 0 #[]

private def elabLetRecDeclValues (view : LetRecView) : TermElabM (Array Expr) :=
view.decls.mapM fun view => do
  forallBoundedTelescope view.type view.numParams fun xs type =>
     withDeclName view.declName do
       value ← elabTermEnsuringType view.valStx type;
       mkLambdaFVars xs value

private def abortIfContainsSyntheticSorry (e : Expr) : TermElabM Unit := do
e ← instantiateMVars e;
when e.hasSyntheticSorry $ throwAbort

private def registerLetRecsToLift (views : Array LetRecDeclView) (fvars : Array Expr) (values : Array Expr) : TermElabM Unit := do
lctx ← getLCtx;
localInsts ← getLocalInstances;
let toLift := views.mapIdx fun i view => {
  ref            := view.ref,
  fvarId         := (fvars.get! i).fvarId!,
  attrs          := view.attrs,
  shortDeclName  := view.shortDeclName,
  declName       := view.declName,
  lctx           := lctx,
  localInstances := localInsts,
  type           := view.type,
  val            := values.get! i,
  mvarId         := view.mvar.mvarId!
  : LetRecToLift };
modify fun s => { s with letRecsToLift := toLift.toList ++ s.letRecsToLift }

@[builtinTermElab «letrec»] def elabLetRec : TermElab :=
fun stx expectedType? => do
  view ← mkLetRecDeclView stx;
  withAuxLocalDecls view.decls fun fvars => do
    values ← elabLetRecDeclValues view;
    body ← elabTermEnsuringType view.body expectedType?;
    registerLetRecsToLift view.decls fvars values;
    mkLetFVars fvars body

end Term
end Elab
end Lean
