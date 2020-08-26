/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Attributes
import Lean.Elab.Binders

namespace Lean
namespace Elab
namespace Term

structure LetRecDecl :=
(attrs : Syntax)
(decl  : Syntax)

structure LetRecView :=
(ref       : Syntax)
(isPartial : Bool)
(decls     : Array LetRecDecl)
(body      : Syntax)

private def mkLetRecView (letRec : Syntax) : LetRecView :=
let decls     := (letRec.getArg 2).getArgs.getSepElems.map fun attrDeclSyntax =>
  { attrs := attrDeclSyntax.getArg 0, decl := (attrDeclSyntax.getArg 1).getArg 0 : LetRecDecl };
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

private def isLetEqnsDecl (d : LetRecDecl) : Bool :=
d.decl.isOfKind `Lean.Parser.Term.letEqnsDecl

private def elabLetRecView (view : LetRecView) (expectedType? : Option Expr) : TermElabM Expr :=
throwError ("WIP " ++ mkNullNode (view.decls.map fun (d : LetRecDecl) => d.decl))

@[builtinTermElab «letrec»] def elabLetRec : TermElab :=
fun stx expectedType? => do
  let view := mkLetRecView stx;
  view.decls.forM fun (d : LetRecDecl) =>
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
