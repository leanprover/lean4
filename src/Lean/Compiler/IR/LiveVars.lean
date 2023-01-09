/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.IR.Basic
import Lean.Compiler.IR.FreeVars

namespace Lean.IR

/-! Remark: in the paper "Counting Immutable Beans" the concepts of
   free and live variables coincide because the paper does *not* consider
   join points. For example, consider the function body `B`
   ```
   let x := ctor_0;
   jmp block_1 x
   ```
   in a context where we have the join point `block_1` defined as
   ```
   block_1 (x : obj) : obj :=
   let z := ctor_0 x y;
   ret z
   ```
   The variable `y` is live in the function body `B` since it occurs in
   `block_1` which is "invoked" by `B`.
-/

namespace IsLive
/--
  We use `State Context` instead of `ReaderT Context Id` because we remove
  non local joint points from `Context` whenever we visit them instead of
  maintaining a set of visited non local join points.

  Remark: we don't need to track local join points because we assume there is
  no variable or join point shadowing in our IR.
-/
abbrev M := StateM LocalContext

abbrev visitVar (w : Index) (x : VarId) : M Bool := pure (HasIndex.visitVar w x)
abbrev visitJP (w : Index) (x : JoinPointId) : M Bool := pure (HasIndex.visitJP w x)
abbrev visitArg (w : Index) (a : Arg) : M Bool := pure (HasIndex.visitArg w a)
abbrev visitArgs (w : Index) (as : Array Arg) : M Bool := pure (HasIndex.visitArgs w as)
abbrev visitExpr (w : Index) (e : Expr) : M Bool := pure (HasIndex.visitExpr w e)

partial def visitFnBody (w : Index) : FnBody → M Bool
  | FnBody.vdecl _ _ v b    => visitExpr w v <||> visitFnBody w b
  | FnBody.jdecl _ _  v b   => visitFnBody w v <||> visitFnBody w b
  | FnBody.set x _ y b      => visitVar w x <||> visitArg w y <||> visitFnBody w b
  | FnBody.uset x _ y b     => visitVar w x <||> visitVar w y <||> visitFnBody w b
  | FnBody.sset x _ _ y _ b => visitVar w x <||> visitVar w y <||> visitFnBody w b
  | FnBody.setTag x _ b     => visitVar w x <||> visitFnBody w b
  | FnBody.inc x _ _ _ b    => visitVar w x <||> visitFnBody w b
  | FnBody.dec x _ _ _ b    => visitVar w x <||> visitFnBody w b
  | FnBody.del x b          => visitVar w x <||> visitFnBody w b
  | FnBody.mdata _ b        => visitFnBody w b
  | FnBody.jmp j ys         => visitArgs w ys <||> do
      let ctx ← get
      match ctx.getJPBody j with
      | some b =>
        -- `j` is not a local join point since we assume we cannot shadow join point declarations.
        -- Instead of marking the join points that we have already been visited, we permanently remove `j` from the context.
        set (ctx.eraseJoinPointDecl j) *> visitFnBody w b
      | none   =>
        -- `j` must be a local join point. So do nothing since we have already visite its body.
        pure false
  | FnBody.ret x            => visitArg w x
  | FnBody.case _ x _ alts  => visitVar w x <||> alts.anyM (fun alt => visitFnBody w alt.body)
  | FnBody.unreachable      => pure false

end IsLive

/-- Return true if `x` is live in the function body `b` in the context `ctx`.

   Remark: the context only needs to contain all (free) join point declarations.

   Recall that we say that a join point `j` is free in `b` if `b` contains
   `FnBody.jmp j ys` and `j` is not local. -/
def FnBody.hasLiveVar (b : FnBody) (ctx : LocalContext) (x : VarId) : Bool :=
  (IsLive.visitFnBody x.idx b).run' ctx

abbrev LiveVarSet   := VarIdSet
abbrev JPLiveVarMap := RBMap JoinPointId LiveVarSet (fun j₁ j₂ => compare j₁.idx j₂.idx)

instance : Inhabited LiveVarSet where
  default := {}

def mkLiveVarSet (x : VarId) : LiveVarSet :=
  RBTree.empty.insert x

namespace LiveVars

abbrev Collector := LiveVarSet → LiveVarSet

@[inline] private def skip : Collector := fun s => s
@[inline] private def collectVar (x : VarId) : Collector := fun s => s.insert x

private def collectArg : Arg → Collector
  | Arg.var x  => collectVar x
  | _          => skip

private def collectArray {α : Type} (as : Array α) (f : α → Collector) : Collector := fun s =>
  as.foldl (fun s a => f a s) s

private def collectArgs (as : Array Arg) : Collector :=
  collectArray as collectArg

private def accumulate (s' : LiveVarSet) : Collector :=
  fun s => s'.fold (fun s x => s.insert x) s

private def collectJP (m : JPLiveVarMap) (j : JoinPointId) : Collector :=
  match m.find? j with
  | some xs => accumulate xs
  | none    => skip -- unreachable for well-formed code

private def bindVar (x : VarId) : Collector := fun s =>
  s.erase x

private def bindParams (ps : Array Param) : Collector := fun s =>
  ps.foldl (fun s p => s.erase p.x) s

def collectExpr : Expr → Collector
  | Expr.ctor _ ys      => collectArgs ys
  | Expr.reset _ x      => collectVar x
  | Expr.reuse x _ _ ys => collectVar x ∘ collectArgs ys
  | Expr.proj _ x       => collectVar x
  | Expr.uproj _ x      => collectVar x
  | Expr.sproj _ _ x    => collectVar x
  | Expr.fap _ ys       => collectArgs ys
  | Expr.pap _ ys       => collectArgs ys
  | Expr.ap x ys        => collectVar x ∘ collectArgs ys
  | Expr.box _ x        => collectVar x
  | Expr.unbox x        => collectVar x
  | Expr.lit _          => skip
  | Expr.isShared x     => collectVar x

partial def collectFnBody : FnBody → JPLiveVarMap → Collector
  | FnBody.vdecl x _ v b,    m => collectExpr v ∘ bindVar x ∘ collectFnBody b m
  | FnBody.jdecl j ys v b,   m =>
    let jLiveVars := (bindParams ys ∘ collectFnBody v m) {};
    let m         := m.insert j jLiveVars;
    collectFnBody b m
  | FnBody.set x _ y b,      m => collectVar x ∘ collectArg y ∘ collectFnBody b m
  | FnBody.setTag x _ b,     m => collectVar x ∘ collectFnBody b m
  | FnBody.uset x _ y b,     m => collectVar x ∘ collectVar y ∘ collectFnBody b m
  | FnBody.sset x _ _ y _ b, m => collectVar x ∘ collectVar y ∘ collectFnBody b m
  | FnBody.inc x _ _ _ b,    m => collectVar x ∘ collectFnBody b m
  | FnBody.dec x _ _ _ b,    m => collectVar x ∘ collectFnBody b m
  | FnBody.del x b,          m => collectVar x ∘ collectFnBody b m
  | FnBody.mdata _ b,        m => collectFnBody b m
  | FnBody.ret x,            _ => collectArg x
  | FnBody.case _ x _ alts,  m => collectVar x ∘ collectArray alts (fun alt => collectFnBody alt.body m)
  | FnBody.unreachable,      _ => skip
  | FnBody.jmp j xs,         m => collectJP m j ∘ collectArgs xs

def updateJPLiveVarMap (j : JoinPointId) (ys : Array Param) (v : FnBody) (m : JPLiveVarMap) : JPLiveVarMap :=
  let jLiveVars := (bindParams ys ∘ collectFnBody v m) {};
  m.insert j jLiveVars

end LiveVars

def updateLiveVars (e : Expr) (v : LiveVarSet) : LiveVarSet :=
  LiveVars.collectExpr e v

def collectLiveVars (b : FnBody) (m : JPLiveVarMap) (v : LiveVarSet := {}) : LiveVarSet :=
  LiveVars.collectFnBody b m v

export LiveVars (updateJPLiveVarMap)

end Lean.IR
