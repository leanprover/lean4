/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.compiler.ir.basic

namespace Lean
namespace IR

namespace MaxIndex
/- Compute the maximum index `M` used in a declaration.
   We `M` to initialize the fresh index generator used to create fresh
   variable and join point names.

   Recall that we variable and join points share the same namespace in
   our implementation.
-/

abbrev Collector := Index → Index

@[inline] private def skip : Collector := id
@[inline] private def collect (x : Index) : Collector := λ y, if x > y then x else y
@[inline] private def collectVar (x : VarId) : Collector := collect x.idx
@[inline] private def collectJP (j : JoinPointId) : Collector := collect j.idx
@[inline] private def seq (k₁ k₂ : Collector) : Collector := k₂ ∘ k₁
instance : HasAndthen Collector := ⟨seq⟩

private def collectArg : Arg → Collector
| (Arg.var x) := collectVar x
| irrelevant  := skip

@[specialize] private def collectArray {α : Type} (as : Array α) (f : α → Collector) : Collector :=
λ m, as.foldl (λ m a, f a m) m

private def collectArgs (as : Array Arg) : Collector := collectArray as collectArg
private def collectParam (p : Param) : Collector := collectVar p.x
private def collectParams (ps : Array Param) : Collector := collectArray ps collectParam

private def collectExpr : Expr → Collector
| (Expr.ctor _ ys)       := collectArgs ys
| (Expr.reset x)         := collectVar x
| (Expr.reuse x _ _ ys)  := collectVar x; collectArgs ys
| (Expr.proj _ x)        := collectVar x
| (Expr.uproj _ x)       := collectVar x
| (Expr.sproj _ _ x)     := collectVar x
| (Expr.fap _ ys)        := collectArgs ys
| (Expr.pap _ ys)        := collectArgs ys
| (Expr.ap x ys)         := collectVar x; collectArgs ys
| (Expr.box _ x)         := collectVar x
| (Expr.unbox x)         := collectVar x
| (Expr.lit v)           := skip
| (Expr.isShared x)      := collectVar x
| (Expr.isTaggedPtr x)   := collectVar x

private def collectAlts (f : FnBody → Collector) (alts : Array Alt) : Collector :=
collectArray alts $ λ alt, f alt.body

partial def collectFnBody : FnBody → Collector
| (FnBody.vdecl x _ v b)    := collectExpr v; collectFnBody b
| (FnBody.jdecl j ys v b)   := collectFnBody v; collectParams ys; collectFnBody b
| (FnBody.set x _ y b)      := collectVar x; collectVar y; collectFnBody b
| (FnBody.uset x _ y b)     := collectVar x; collectVar y; collectFnBody b
| (FnBody.sset x _ _ y _ b) := collectVar x; collectVar y; collectFnBody b
| (FnBody.release x _ b)    := collectVar x; collectFnBody b
| (FnBody.inc x _ _ b)      := collectVar x; collectFnBody b
| (FnBody.dec x _ _ b)      := collectVar x; collectFnBody b
| (FnBody.mdata _ b)        := collectFnBody b
| (FnBody.case _ x alts)    := collectVar x; collectAlts collectFnBody alts
| (FnBody.jmp j ys)         := collectJP j; collectArgs ys
| (FnBody.ret x)            := collectArg x
| FnBody.unreachable        := skip

partial def collectDecl : Decl → Collector
| (Decl.fdecl _ xs _ b)  := collectParams xs; collectFnBody b
| (Decl.extern _ xs _ _) := collectParams xs

end MaxIndex

def FnBody.maxIndex (b : FnBody) : Index :=
MaxIndex.collectFnBody b 0

def Decl.maxIndex (d : Decl) : Index :=
MaxIndex.collectDecl d 0

namespace FreeIndices
/- We say a variable (join point) index (aka name) is free in a function body
   if there isn't a `FnBody.vdecl` (`Fnbody.jdecl`) binding it. -/

abbrev Collector := IndexSet → IndexSet → IndexSet

@[inline] private def skip : Collector :=
λ bv fv, fv

@[inline] private def collectIndex (x : Index) : Collector :=
λ bv fv, if bv.contains x then fv else fv.insert x

@[inline] private def collectVar (x : VarId) : Collector :=
collectIndex x.idx

@[inline] private def collectJP (x : JoinPointId) : Collector :=
collectIndex x.idx

@[inline] private def withIndex (x : Index) : Collector → Collector :=
λ k bv fv, k (bv.insert x) fv

@[inline] private def withVar (x : VarId) : Collector → Collector :=
withIndex x.idx

@[inline] private def withJP (x : JoinPointId) : Collector → Collector :=
withIndex x.idx

def insertParams (s : IndexSet) (ys : Array Param) : IndexSet :=
ys.foldl (λ s p, s.insert p.x.idx) s

@[inline] private def withParams (ys : Array Param) : Collector → Collector :=
λ k bv fv, k (insertParams bv ys) fv

@[inline] private def seq : Collector → Collector → Collector :=
λ k₁ k₂ bv fv, k₂ bv (k₁ bv fv)

instance : HasAndthen Collector := ⟨seq⟩

private def collectArg : Arg → Collector
| (Arg.var x) := collectVar x
| irrelevant  := skip

@[specialize] private def collectArray {α : Type} (as : Array α) (f : α → Collector) : Collector :=
λ bv fv, as.foldl (λ fv a, f a bv fv) fv

private def collectArgs (as : Array Arg) : Collector :=
collectArray as collectArg

private def collectExpr : Expr → Collector
| (Expr.ctor _ ys)       := collectArgs ys
| (Expr.reset x)         := collectVar x
| (Expr.reuse x _ _ ys)  := collectVar x; collectArgs ys
| (Expr.proj _ x)        := collectVar x
| (Expr.uproj _ x)       := collectVar x
| (Expr.sproj _ _ x)     := collectVar x
| (Expr.fap _ ys)        := collectArgs ys
| (Expr.pap _ ys)        := collectArgs ys
| (Expr.ap x ys)         := collectVar x; collectArgs ys
| (Expr.box _ x)         := collectVar x
| (Expr.unbox x)         := collectVar x
| (Expr.lit v)           := skip
| (Expr.isShared x)      := collectVar x
| (Expr.isTaggedPtr x)   := collectVar x

private def collectAlts (f : FnBody → Collector) (alts : Array Alt) : Collector :=
collectArray alts $ λ alt, f alt.body

partial def collectFnBody : FnBody → Collector
| (FnBody.vdecl x _ v b)    := collectExpr v; withVar x (collectFnBody b)
| (FnBody.jdecl j ys v b)   := withParams ys (collectFnBody v); withJP j (collectFnBody b)
| (FnBody.set x _ y b)      := collectVar x; collectVar y; collectFnBody b
| (FnBody.uset x _ y b)     := collectVar x; collectVar y; collectFnBody b
| (FnBody.sset x _ _ y _ b) := collectVar x; collectVar y; collectFnBody b
| (FnBody.release x _ b)    := collectVar x; collectFnBody b
| (FnBody.inc x _ _ b)      := collectVar x; collectFnBody b
| (FnBody.dec x _ _ b)      := collectVar x; collectFnBody b
| (FnBody.mdata _ b)        := collectFnBody b
| (FnBody.case _ x alts)    := collectVar x; collectAlts collectFnBody alts
| (FnBody.jmp j ys)         := collectJP j; collectArgs ys
| (FnBody.ret x)            := collectArg x
| FnBody.unreachable        := skip

end FreeIndices

def FnBody.collectFreeIndices (b : FnBody) (vs : IndexSet) : IndexSet :=
FreeIndices.collectFnBody b {} vs

def FnBody.freeIndices (b : FnBody) : IndexSet :=
b.collectFreeIndices {}

namespace HasIndex
/- In principle, we can check whether a function body `b` contains an index `i` using
   `b.freeIndices.contains i`, but it is more efficient to avoid the construction
   of the set of freeIndices and just search whether `i` occurs in `b` or not.
-/
def visitVar (w : Index) (x : VarId) : Bool := w == x.idx
def visitJP (w : Index) (x : JoinPointId) : Bool := w == x.idx

def visitArg (w : Index) : Arg → Bool
| (Arg.var x) := visitVar w x
| _           := false

def visitArgs (w : Index) (xs : Array Arg) : Bool :=
xs.any (visitArg w)

def visitParams (w : Index) (ps : Array Param) : Bool :=
ps.any (λ p, w == p.x.idx)

def visitExpr (w : Index) : Expr → Bool
| (Expr.ctor _ ys)       := visitArgs w ys
| (Expr.reset x)         := visitVar w x
| (Expr.reuse x _ _ ys)  := visitVar w x || visitArgs w ys
| (Expr.proj _ x)        := visitVar w x
| (Expr.uproj _ x)       := visitVar w x
| (Expr.sproj _ _ x)     := visitVar w x
| (Expr.fap _ ys)        := visitArgs w ys
| (Expr.pap _ ys)        := visitArgs w ys
| (Expr.ap x ys)         := visitVar w x || visitArgs w ys
| (Expr.box _ x)         := visitVar w x
| (Expr.unbox x)         := visitVar w x
| (Expr.lit v)           := false
| (Expr.isShared x)      := visitVar w x
| (Expr.isTaggedPtr x)   := visitVar w x

partial def visitFnBody (w : Index) : FnBody → Bool
| (FnBody.vdecl x _ v b)    := visitExpr w v || visitFnBody b
| (FnBody.jdecl j ys v b)   := visitFnBody v || visitFnBody b
| (FnBody.set x _ y b)      := visitVar w x || visitVar w y || visitFnBody b
| (FnBody.uset x _ y b)     := visitVar w x || visitVar w y || visitFnBody b
| (FnBody.sset x _ _ y _ b) := visitVar w x || visitVar w y || visitFnBody b
| (FnBody.release x _ b)    := visitVar w x || visitFnBody b
| (FnBody.inc x _ _ b)      := visitVar w x || visitFnBody b
| (FnBody.dec x _ _ b)      := visitVar w x || visitFnBody b
| (FnBody.mdata _ b)        := visitFnBody b
| (FnBody.jmp j ys)         := visitJP w j || visitArgs w ys
| (FnBody.ret x)            := visitArg w x
| (FnBody.case _ x alts)    := visitVar w x || alts.any (λ alt, visitFnBody alt.body)
| (FnBody.unreachable)      := false

end HasIndex

def Arg.hasFreeVar (arg : Arg) (x : VarId) : Bool := HasIndex.visitArg x.idx arg
def Expr.hasFreeVar (e : Expr) (x : VarId) : Bool := HasIndex.visitExpr x.idx e
def FnBody.hasFreeVar (b : FnBody) (x : VarId) : Bool := HasIndex.visitFnBody x.idx b

end IR
end Lean
