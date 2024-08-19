/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Compiler.InitAttr
import Lean.Compiler.IR.CompilerM

/-! # Helper functions for backend code generators -/

namespace Lean.IR
/-- Return true iff `b` is of the form `let x := g ys; ret x` -/
def isTailCallTo (g : Name) (b : FnBody) : Bool :=
  match b with
  | FnBody.vdecl x _ (Expr.fap f _) (FnBody.ret (Arg.var y)) => x == y && f == g
  | _  => false

def usesModuleFrom (env : Environment) (modulePrefix : Name) : Bool :=
  env.allImportedModuleNames.toList.any fun modName => modulePrefix.isPrefixOf modName

namespace CollectUsedDecls

abbrev M := ReaderT Environment (StateM NameSet)

@[inline] def collect (f : FunId) : M Unit :=
  modify fun s => s.insert f

partial def collectFnBody : FnBody → M Unit
  | .vdecl _ _ v b   =>
    match v with
    | .fap f _ => collect f *> collectFnBody b
    | .pap f _ => collect f *> collectFnBody b
    | _        => collectFnBody b
  | .jdecl _ _ v b   => collectFnBody v *> collectFnBody b
  | .case _ _ _ alts => alts.forM fun alt => collectFnBody alt.body
  | e => do unless e.isTerminal do collectFnBody e.body

def collectInitDecl (fn : Name) : M Unit := do
  let env ← read
  match getInitFnNameFor? env fn with
  | some initFn => collect initFn
  | _           => pure ()

def collectDecl : Decl → M NameSet
  | .fdecl (f := f) (body := b) .. => collectInitDecl f *> CollectUsedDecls.collectFnBody b *> get
  | .extern (f := f) .. => collectInitDecl f *> get

end CollectUsedDecls

def collectUsedDecls (env : Environment) (decl : Decl) (used : NameSet := {}) : NameSet :=
  (CollectUsedDecls.collectDecl decl env).run' used

abbrev VarTypeMap  := Std.HashMap VarId IRType
abbrev JPParamsMap := Std.HashMap JoinPointId (Array Param)

namespace CollectMaps
abbrev Collector := (VarTypeMap × JPParamsMap) → (VarTypeMap × JPParamsMap)
@[inline] def collectVar (x : VarId) (t : IRType) : Collector
  | (vs, js) => (vs.insert x t, js)
def collectParams (ps : Array Param) : Collector :=
  fun s => ps.foldl (fun s p => collectVar p.x p.ty s) s
@[inline] def collectJP (j : JoinPointId) (xs : Array Param) : Collector
  | (vs, js) => (vs, js.insert j xs)

/-- `collectFnBody` assumes the variables in -/
partial def collectFnBody : FnBody → Collector
  | .vdecl x t _ b    => collectVar x t ∘ collectFnBody b
  | .jdecl j xs v b   => collectJP j xs ∘ collectParams xs ∘ collectFnBody v ∘ collectFnBody b
  | .case _ _ _ alts  => fun s => alts.foldl (fun s alt => collectFnBody alt.body s) s
  | e                 => if e.isTerminal then id else collectFnBody e.body

def collectDecl : Decl → Collector
  | .fdecl (xs := xs) (body := b) .. => collectParams xs ∘ collectFnBody b
  | _ => id

end CollectMaps

/-- Return a pair `(v, j)`, where `v` is a mapping from variable/parameter to type,
   and `j` is a mapping from join point to parameters.
   This function assumes `d` has normalized indexes (see `normids.lean`). -/
def mkVarJPMaps (d : Decl) : VarTypeMap × JPParamsMap :=
  CollectMaps.collectDecl d ({}, {})

end IR
end Lean
