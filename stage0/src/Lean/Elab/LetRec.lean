/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Attributes
import Lean.Elab.Binders
import Lean.Elab.DeclModifiers

namespace Lean
namespace Elab
namespace Term

structure LetRecDeclView :=
(attrs : Syntax)
(decl  : Syntax)

structure LetRecView :=
(ref       : Syntax)
(isPartial : Bool)
(decls     : Array LetRecDeclView)
(body      : Syntax)

private def mkLetRecView (letRec : Syntax) : LetRecView :=
let decls     := (letRec.getArg 2).getArgs.getSepElems.map fun attrDeclSyntax =>
  { attrs := attrDeclSyntax.getArg 0, decl := (attrDeclSyntax.getArg 1).getArg 0 : LetRecDeclView };
{ decls     := decls,
  ref       := letRec,
  isPartial := !(letRec.getArg 1).isNone,
  body      := letRec.getArg 4 }

def LetRecView.review (view : LetRecView) : Syntax :=
let result := view.ref;
let result := result.setArg 4 view.body;
let result :=
  if view.isPartial then
    if (result.getArg 1).isNone then
      result.setArg 1 (mkNullNode #[mkAtomFrom result "partial "])
    else
      result
  else
    result.setArg 1 mkNullNode;
let result := result.setArg 2 $ mkSepStx
    (view.decls.map fun decl => mkNullNode #[decl.attrs, mkNode `Lean.Parser.Term.letDecl #[decl.decl]])
    (mkAtomFrom result ", ");
result

private def isLetEqnsDecl (d : LetRecDeclView) : Bool :=
d.decl.isOfKind `Lean.Parser.Term.letEqnsDecl

open Meta

structure LetRecDeclHeader :=
(declName   : Name)
(name       : Name)
(type       : Expr)
(numBinders : Nat)

instance LetRecDeclHeader.inhabited : Inhabited LetRecDeclHeader := ⟨⟨arbitrary _, arbitrary _, arbitrary _, arbitrary _⟩⟩

private def mkLetRecDeclHeaders (view : LetRecView) : TermElabM (Array LetRecDeclHeader) := do
view.decls.mapM fun d =>
  let decl := d.decl;
  withRef decl do
    let declView := mkLetIdDeclView decl;
    (type, numBinders) ← elabBinders declView.binders $ fun xs => do {
        type ← elabType declView.type;
        type ← mkForallFVars xs type;
        pure (type, xs.size)
    };
    currDeclName? ← getDeclName?;
    let declName := currDeclName?.getD Name.anonymous ++ declView.id;
    checkNotAlreadyDeclared declName;
    pure { declName := declName, name := declView.id, type := type, numBinders := numBinders }

private partial def withAuxLocalDeclsAux {α} (headers : Array LetRecDeclHeader) (k : Unit → TermElabM α) : Nat → TermElabM α
| i =>
  if h : i < headers.size then
    let header := headers.get ⟨i, h⟩;
    withLocalDeclD header.name header.type fun _ => withAuxLocalDeclsAux (i+1)
  else
    k ()

private partial def withAuxLocalDecls {α} (headers : Array LetRecDeclHeader) (k : Unit → TermElabM α) : TermElabM α :=
withAuxLocalDeclsAux headers k 0

private def elabLetRecDeclValues (view : LetRecView) (headers : Array LetRecDeclHeader) : TermElabM (Array Expr) :=
view.decls.mapIdxM fun i d => do
  let decl       := d.decl;
  let view       := mkLetIdDeclView decl;
  let header     := headers.get! i;
  forallBoundedTelescope header.type header.numBinders fun xs type =>
     withDeclName header.declName do
       value ← elabTermEnsuringType view.value type;
       mkLambdaFVars xs value

structure LetRecDecl :=
(name     : Name)
(type     : Expr)
(value    : Expr)

private def abortIfContainsSyntheticSorry (e : Expr) : TermElabM Unit := do
e ← instantiateMVars e;
when e.hasSyntheticSorry $ throwError e

private def elabLetRecView (view : LetRecView) (expectedType? : Option Expr) : TermElabM Expr := do
decls ← withSynthesize do {
  headers ← mkLetRecDeclHeaders view;
  withAuxLocalDecls headers fun _ => do
    values ← elabLetRecDeclValues view headers;
    synthesizeSyntheticMVarsNoPostponing;
    -- We abort if there are synthetic sorry's
    values.forM abortIfContainsSyntheticSorry;
    headers.forM fun header => abortIfContainsSyntheticSorry header.type;
    -- TODO
    -- values.forM IO.println;
    values.mapIdxM fun i value => do
      let header := headers.get! i;
      pure { name := header.name, type := header.type, value := value : LetRecDecl }
};
throwError ("WIP")

@[builtinTermElab «letrec»] def elabLetRec : TermElab :=
fun stx expectedType? => do
  let view := mkLetRecView stx;
  view.decls.forM fun (d : LetRecDeclView) =>
    when ((d.decl.getArg 0).isOfKind `Lean.Parser.Term.letPatDecl) $
      throwErrorAt d.decl "patterns are not allowed in letrec expressions";
  if view.decls.any isLetEqnsDecl then do
    newDecls ← view.decls.mapM fun d =>
      if isLetEqnsDecl d then do
        newDecl ← liftMacroM $ expandLetEqnsDecl d.decl;
        pure { d with decl := newDecl }
      else
        pure d;
    let stxNew := { view with decls := newDecls }.review;
    withMacroExpansion stx stxNew $ elabTerm stxNew expectedType?
  else
    elabLetRecView view expectedType?

end Term
end Elab
end Lean
