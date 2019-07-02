/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.control.conditional
import init.lean.compiler.initattr
import init.lean.compiler.ir.compilerm

/- Helper functions for backend code generators -/

namespace Lean
namespace IR
/- Return true iff `b` is of the form `let x := g ys; ret x` -/
def isTailCallTo (g : Name) (b : FnBody) : Bool :=
match b with
| FnBody.vdecl x _ (Expr.fap f _) (FnBody.ret (Arg.var y)) := x == y && f == g
| _  := false

namespace UsesLeanNamespace

abbrev M := ReaderT Environment (State NameSet)

def leanNameSpacePrefix := `Lean

partial def visitFnBody : FnBody → M Bool
| (FnBody.vdecl _ _ v b) :=
  let checkFn (f : FunId) : M Bool :=
     if leanNameSpacePrefix.isPrefixOf f then pure true
     else do {
       s ← get;
       if s.contains f then
         visitFnBody b
       else do
         modify (fun s => s.insert f);
         env ← read;
         match findEnvDecl env f with
         | some (Decl.fdecl _ _ _ fbody) := visitFnBody fbody <||> visitFnBody b
         | other                         := visitFnBody b
    };
  match v with
  | Expr.fap f _ := checkFn f
  | Expr.pap f _ := checkFn f
  | other        := visitFnBody b
| (FnBody.jdecl _ _ v b) := visitFnBody v <||> visitFnBody b
| (FnBody.case _ _ alts) := alts.anyM $ fun alt => visitFnBody alt.body
| e :=
  if e.isTerminal then pure false
  else visitFnBody e.body

end UsesLeanNamespace

def usesLeanNamespace (env : Environment) : Decl → Bool
| (Decl.fdecl _ _ _ b) := (UsesLeanNamespace.visitFnBody b env).run' {}
| _                    := false


namespace CollectUsedDecls

abbrev M := ReaderT Environment (State NameSet)

@[inline] def collect (f : FunId) : M Unit :=
modify (fun s => s.insert f)

partial def collectFnBody : FnBody → M Unit
| (FnBody.vdecl _ _ v b) :=
  match v with
  | Expr.fap f _ := collect f *> collectFnBody b
  | Expr.pap f _ := collect f *> collectFnBody b
  | other        := collectFnBody b
| (FnBody.jdecl _ _ v b) := collectFnBody v *> collectFnBody b
| (FnBody.case _ _ alts) := alts.mfor $ fun alt => collectFnBody alt.body
| e := unless e.isTerminal $ collectFnBody e.body

def collectInitDecl (fn : Name) : M Unit :=
do env ← read;
   match getInitFnNameFor env fn with
   | some initFn := collect initFn
   | _           := pure ()

def collectDecl : Decl → M NameSet
| (Decl.fdecl fn _ _ b)  := collectInitDecl fn *> CollectUsedDecls.collectFnBody b *> get
| (Decl.extern fn _ _ _) := collectInitDecl fn *> get

end CollectUsedDecls

def collectUsedDecls (env : Environment) (decl : Decl) (used : NameSet := {}) : NameSet :=
(CollectUsedDecls.collectDecl decl env).run' used

abbrev VarTypeMap  := HashMap VarId IRType
abbrev JPParamsMap := HashMap JoinPointId (Array Param)

namespace CollectMaps
abbrev Collector := (VarTypeMap × JPParamsMap) → (VarTypeMap × JPParamsMap)
@[inline] def collectVar (x : VarId) (t : IRType) : Collector
| (vs, js) := (vs.insert x t, js)
def collectParams (ps : Array Param) : Collector :=
fun s => ps.foldl (fun s p => collectVar p.x p.ty s) s
@[inline] def collectJP (j : JoinPointId) (xs : Array Param) : Collector
| (vs, js) := (vs, js.insert j xs)

/- `collectFnBody` assumes the variables in -/
partial def collectFnBody : FnBody → Collector
| (FnBody.vdecl x t _ b)  := collectVar x t ∘ collectFnBody b
| (FnBody.jdecl j xs v b) := collectJP j xs ∘ collectParams xs ∘ collectFnBody v ∘ collectFnBody b
| (FnBody.case _ _ alts)  := fun s => alts.foldl (fun s alt => collectFnBody alt.body s) s
| e                       := if e.isTerminal then id else collectFnBody e.body

def collectDecl : Decl → Collector
| (Decl.fdecl _ xs _ b) := collectParams xs ∘ collectFnBody b
| _ := id

end CollectMaps

/- Return a pair `(v, j)`, where `v` is a mapping from variable/parameter to type,
   and `j` is a mapping from join point to parameters.
   This function assumes `d` has normalized indexes (see `normids.lean`). -/
def mkVarJPMaps (d : Decl) : VarTypeMap × JPParamsMap :=
CollectMaps.collectDecl d ({}, {})

end IR
end Lean
