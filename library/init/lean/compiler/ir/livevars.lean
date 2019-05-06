/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.compiler.ir.basic
import init.lean.compiler.ir.freevars
import init.control.reader
import init.control.conditional

namespace Lean
namespace IR

/- Remark: in the paper "Counting Immutable Beans" the concepts of
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
   ``
   The variable `y` is live in the function body `B` since it occurs in
   `block_1` which is "invoked" by `B`.
-/

namespace IsLive
/-
  IndexSet is the set of local joint points
  We use `State Context` instead of `ReaderT Context Id` because we remove
  non local joint points from `Context` whenever we visit them instead of
  maintaining a set of visit non local join points.
-/
abbrev M := ReaderT IndexSet (State Context)

@[inline] def visitVar (w : Index) (x : VarId) : M Bool := pure (HasIndex.visitVar w x)
@[inline] def visitJP (w : Index) (x : JoinPointId) : M Bool := pure (HasIndex.visitJP w x)
@[inline] def visitArg (w : Index) (a : Arg) : M Bool := pure (HasIndex.visitArg w a)
@[inline] def visitArgs (w : Index) (as : Array Arg) : M Bool := pure (HasIndex.visitArgs w as)
@[inline] def visitExpr (w : Index) (e : Expr) : M Bool := pure (HasIndex.visitExpr w e)

/- Search for `w` using `k` in a context where variable `x` is declared. -/
@[inline] def withVDecl (x : VarId) (w : Index) (k : M Bool) : M Bool :=
if w == x.idx then pure false
else k

/- Search for `w` using `k` in a context where joint point `x` is declared. -/
@[inline] def withJDecl (j : JoinPointId) (w : Index) (k : M Bool) : M Bool :=
if w == j.idx then pure false
else adaptReader (λ localJPs : IndexSet, localJPs.insert j.idx) k

/- Search for `w` using `k` in a context with `ys` parameters -/
@[inline] def withParams (ys : Array Param) (w : Index) (k : M Bool) : M Bool :=
if HasIndex.visitParams w ys then pure false
else k

local attribute [instance] monadInhabited

partial def visitFnBody (w : Index) : FnBody → M Bool
| (FnBody.vdecl x _ v b)    := visitExpr w v <||> withVDecl x w (visitFnBody b)
| (FnBody.jdecl j ys _ v b) := withParams ys w (visitFnBody v) <||> withJDecl j w (visitFnBody b)
| (FnBody.set x _ y b)      := visitVar w x <||> visitVar w y <||> visitFnBody b
| (FnBody.uset x _ y b)     := visitVar w x <||> visitVar w y <||> visitFnBody b
| (FnBody.sset x _ _ y _ b) := visitVar w x <||> visitVar w y <||> visitFnBody b
| (FnBody.release x _ b)    := visitVar w x <||> visitFnBody b
| (FnBody.inc x _ _ b)      := visitVar w x <||> visitFnBody b
| (FnBody.dec x _ _ b)      := visitVar w x <||> visitFnBody b
| (FnBody.mdata _ b)        := visitFnBody b
| (FnBody.jmp j ys)         := visitArgs w ys <||> do {
  localJPs ← read,
  if localJPs.contains j.idx then pure false -- `j` is a local joint point, so we have already searched for `w` in its declaration.
  else do
    ctx ← get,
    match ctx.find j.idx with
    | some b :=
      -- `j` is not a local join point.
      -- Instead of marking the join points that we have already been visited, we permanently remove `j` from the context.
      set (ctx.erase j.idx) *> visitFnBody b
    | none   := pure false
  }
| (FnBody.ret x)            := visitArg w x
| (FnBody.case _ x alts)    := visitVar w x <||> alts.anyM (λ alt, visitFnBody alt.body)
| (FnBody.unreachable)      := pure false

end IsLive

/- Return true if `x` is live in the function body `b` in the context `ctx`.

   Remark: the context only needs to contain all (free) join point declarations.

   Recall that we say that a join point `j` is free in `b` if `b` contains
   `FnBody.jmp j ys` and `j` is not local. -/
def FnBody.isLive (b : FnBody) (ctx : Context) (x : VarId) : Bool :=
(IsLive.visitFnBody x.idx b {}).run' ctx

end IR
end Lean
