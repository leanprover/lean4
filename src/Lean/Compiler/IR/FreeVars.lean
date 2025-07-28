/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Compiler.IR.Basic

public section

namespace Lean.IR

namespace MaxIndex
/-! Compute the maximum index `M` used in a declaration.
   We `M` to initialize the fresh index generator used to create fresh
   variable and join point names.

   Recall that we variable and join points share the same namespace in
   our implementation.
-/

abbrev Collector := Index → Index

@[inline] private def skip : Collector := id
@[inline] private def collect (x : Index) : Collector := fun y => if x > y then x else y
@[inline] private def collectVar (x : VarId) : Collector := collect x.idx
@[inline] private def collectJP (j : JoinPointId) : Collector := collect j.idx
@[inline] private def seq (k₁ k₂ : Collector) : Collector := k₂ ∘ k₁
instance : AndThen Collector where
  andThen a b := private seq a (b ())

private def collectArg : Arg → Collector
  | .var x  => collectVar x
  | .erased => skip

private def collectArray {α : Type} (as : Array α) (f : α → Collector) : Collector :=
  fun m => as.foldl (fun m a => f a m) m

private def collectArgs (as : Array Arg) : Collector := collectArray as collectArg
private def collectParam (p : Param) : Collector := collectVar p.x
private def collectParams (ps : Array Param) : Collector := collectArray ps collectParam

private def collectExpr : Expr → Collector
  | .proj _ x | .uproj _ x | .sproj _ _ x | .box _ x | .unbox x | .reset _ x | .isShared x =>
    collectVar x
  | .ctor _ ys | .fap _ ys | .pap _ ys =>
    collectArgs ys
  | .ap x ys | .reuse x _ _ ys =>
    collectVar x >> collectArgs ys
  | .lit _ => skip

private def collectAlts (f : FnBody → Collector) (alts : Array Alt) : Collector :=
  collectArray alts fun alt => f alt.body

partial def collectFnBody : FnBody → Collector
  | .vdecl x _ v b =>
    collectVar x >> collectExpr v >> collectFnBody b
  | .jdecl j ys v b =>
    collectJP j >> collectFnBody v >> collectParams ys >> collectFnBody b
  | .set x _ y b =>
    collectVar x >> collectArg y >> collectFnBody b
  | .uset x _ y b | .sset x _ _ y _ b =>
    collectVar x >> collectVar y >> collectFnBody b
  | .setTag x _ b | .inc x _ _ _ b | .dec x _ _ _ b | .del x b =>
    collectVar x >> collectFnBody b
  | .case _ x _ alts =>
    collectVar x >> collectAlts collectFnBody alts
  | .jmp j ys =>
    collectJP j >> collectArgs ys
  | .ret x =>
    collectArg x
  | .unreachable => skip

partial def collectDecl : Decl → Collector
  | .fdecl (xs := xs) (body := b) .. => collectParams xs >> collectFnBody b
  | .extern (xs := xs) ..            => collectParams xs

end MaxIndex

def FnBody.maxIndex (b : FnBody) : Index :=
  MaxIndex.collectFnBody b 0

def Decl.maxIndex (d : Decl) : Index :=
  MaxIndex.collectDecl d 0

namespace FreeIndices
/-! We say a variable (join point) index (aka name) is free in a function body
   if there isn't a `FnBody.vdecl` (`Fnbody.jdecl`) binding it. -/

abbrev Collector := IndexSet → IndexSet → IndexSet

@[inline] private def skip : Collector :=
  fun _ fv => fv

@[inline] private def collectIndex (x : Index) : Collector :=
  fun bv fv => if bv.contains x then fv else fv.insert x

@[inline] private def collectVar (x : VarId) : Collector :=
  collectIndex x.idx

@[inline] private def collectJP (x : JoinPointId) : Collector :=
  collectIndex x.idx

@[inline] private def withIndex (x : Index) : Collector → Collector :=
  fun k bv fv => k (bv.insert x) fv

@[inline] private def withVar (x : VarId) : Collector → Collector :=
  withIndex x.idx

@[inline] private def withJP (x : JoinPointId) : Collector → Collector :=
  withIndex x.idx

def insertParams (s : IndexSet) (ys : Array Param) : IndexSet :=
  ys.foldl (init := s) fun s p => s.insert p.x.idx

@[inline] private def withParams (ys : Array Param) : Collector → Collector :=
  fun k bv fv => k (insertParams bv ys) fv

@[inline] private def seq : Collector → Collector → Collector :=
  fun k₁ k₂ bv fv => k₂ bv (k₁ bv fv)

instance : AndThen Collector where
  andThen a b := private seq a (b ())

private def collectArg : Arg → Collector
  | .var x  => collectVar x
  | .erased => skip

private def collectArray {α : Type} (as : Array α) (f : α → Collector) : Collector :=
  fun bv fv => as.foldl (fun fv a => f a bv fv) fv

private def collectArgs (as : Array Arg) : Collector :=
  collectArray as collectArg

private def collectExpr : Expr → Collector
  | .proj _ x | .uproj _ x | .sproj _ _ x | .box _ x | .unbox x | .reset _ x | .isShared x =>
    collectVar x
  | .ctor _ ys | .fap _ ys | .pap _ ys =>
    collectArgs ys
  | .ap x ys | .reuse x _ _ ys =>
    collectVar x >> collectArgs ys
  | .lit _ => skip

private def collectAlts (f : FnBody → Collector) (alts : Array Alt) : Collector :=
  collectArray alts fun alt => f alt.body

partial def collectFnBody : FnBody → Collector
  | .vdecl x _ v b =>
    collectExpr v >> withVar x (collectFnBody b)
  | .jdecl j ys v b =>
    withParams ys (collectFnBody v) >> withJP j (collectFnBody b)
  | .set x _ y b =>
    collectVar x >> collectArg y >> collectFnBody b
  | .uset x _ y b | .sset x _ _ y _ b =>
    collectVar x >> collectVar y >> collectFnBody b
  | .setTag x _ b | .inc x _ _ _ b | .dec x _ _ _ b | .del x b =>
    collectVar x >> collectFnBody b
  | .case _ x _ alts =>
    collectVar x >>
      collectAlts collectFnBody alts
  | .jmp j ys =>
    collectJP j >> collectArgs ys
  | .ret x =>
    collectArg x
  | .unreachable => skip

end FreeIndices

def FnBody.collectFreeIndices (b : FnBody) (vs : IndexSet) : IndexSet :=
  FreeIndices.collectFnBody b {} vs

def FnBody.freeIndices (b : FnBody) : IndexSet :=
  b.collectFreeIndices {}

namespace HasIndex
/-! In principle, we can check whether a function body `b` contains an index `i` using
   `b.freeIndices.contains i`, but it is more efficient to avoid the construction
   of the set of freeIndices and just search whether `i` occurs in `b` or not.
-/
def visitVar (w : Index) (x : VarId) : Bool := w == x.idx
def visitJP (w : Index) (x : JoinPointId) : Bool := w == x.idx

def visitArg (w : Index) : Arg → Bool
  | .var x => visitVar w x
  | .erased => false

def visitArgs (w : Index) (xs : Array Arg) : Bool :=
  xs.any (visitArg w)

def visitParams (w : Index) (ps : Array Param) : Bool :=
  ps.any (fun p => w == p.x.idx)

def visitExpr (w : Index) : Expr → Bool
  | .proj _ x | .uproj _ x | .sproj _ _ x | .box _ x | .unbox x | .reset _ x | .isShared x =>
    visitVar w x
  | .ctor _ ys | .fap _ ys | .pap _ ys =>
    visitArgs w ys
  | .ap x ys | .reuse x _ _ ys =>
    visitVar w x || visitArgs w ys
  | .lit _ => false

partial def visitFnBody (w : Index) : FnBody → Bool
  | .vdecl _ _ v b =>
    visitExpr w v || visitFnBody w b
  | .jdecl _ _  v b =>
    visitFnBody w v || visitFnBody w b
  | FnBody.set x _ y b =>
    visitVar w x || visitArg w y || visitFnBody w b
  | .uset x _ y b | .sset x _ _ y _ b =>
    visitVar w x || visitVar w y || visitFnBody w b
  | .setTag x _ b | .inc x _ _ _ b | .dec x _ _ _ b | .del x b =>
    visitVar w x || visitFnBody w b
  | .case _ x _ alts =>
    visitVar w x || alts.any (fun alt => visitFnBody w alt.body)
  | .jmp j ys =>
    visitJP w j || visitArgs w ys
  | .ret x =>
    visitArg w x
  | .unreachable => false

end HasIndex

def Arg.hasFreeVar (arg : Arg) (x : VarId) : Bool := HasIndex.visitArg x.idx arg
def Expr.hasFreeVar (e : Expr) (x : VarId) : Bool := HasIndex.visitExpr x.idx e
def FnBody.hasFreeVar (b : FnBody) (x : VarId) : Bool := HasIndex.visitFnBody x.idx b

end Lean.IR
