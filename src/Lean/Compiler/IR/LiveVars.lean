/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Compiler.IR.Basic
public import Lean.Compiler.IR.FreeVars

public section

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
  non local join points from `Context` whenever we visit them instead of
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
  | .vdecl _ _ v b =>
    visitExpr w v <||> visitFnBody w b
  | .jdecl _ _  v b =>
    visitFnBody w v <||> visitFnBody w b
  | .set x _ y b =>
    visitVar w x <||> visitArg w y <||> visitFnBody w b
  | .uset x _ y b | .sset x _ _ y _ b =>
    visitVar w x <||> visitVar w y <||> visitFnBody w b
  | .setTag x _ b | .inc x _ _ _ b | .dec x _ _ _ b | .del x b =>
    visitVar w x <||> visitFnBody w b
  | .case _ x _ alts =>
    visitVar w x <||> alts.anyM (fun alt => visitFnBody w alt.body)
  | .jmp j ys =>
    visitArgs w ys <||> do
      let ctx ← get
      match ctx.getJPBody j with
      | some b =>
        -- `j` is not a local join point since we assume we cannot shadow join point declarations.
        -- Instead of marking the join points that we have already been visited, we permanently remove `j` from the context.
        set (ctx.eraseJoinPointDecl j) *> visitFnBody w b
      | none   =>
        -- `j` must be a local join point. So do nothing since we have already visite its body.
        pure false
  | .ret x =>
    visitArg w x
  | .unreachable => pure false

end IsLive

/-- Return true if `x` is live in the function body `b` in the context `ctx`.

   Remark: the context only needs to contain all (free) join point declarations.

   Recall that we say that a join point `j` is free in `b` if `b` contains
   `FnBody.jmp j ys` and `j` is not local. -/
def FnBody.hasLiveVar (b : FnBody) (ctx : LocalContext) (x : VarId) : Bool :=
  (IsLive.visitFnBody x.idx b).run' ctx

abbrev LiveVarSet   := VarIdSet
abbrev JPLiveVarMap := Std.TreeMap JoinPointId LiveVarSet (fun j₁ j₂ => compare j₁.idx j₂.idx)

def mkLiveVarSet (x : VarId) : LiveVarSet :=
  Std.TreeSet.empty.insert x

namespace LiveVars

structure State where
  liveVars : LiveVarSet := {}

abbrev M := StateM State

private def useVar (x : VarId) : M Unit := do
  modify fun s => { s with liveVars := s.liveVars.insert x }

private def bindVar (x : VarId) : M Unit := do
  modify fun s => { s with liveVars := s.liveVars.erase x }

private def useArg (arg : Arg) : M Unit :=
  match arg with
  | .var x => useVar x
  | .erased => pure ()

private def bindParams (ps : Array Param) : M Unit := do
  ps.forM (bindVar ·.x)

private def visitJP (m : JPLiveVarMap) (j : JoinPointId) : M Unit :=
  m.get? j |>.forM fun xs =>
    modify fun s => { s with liveVars := s.liveVars.merge xs }

private def useExpr (e : Expr) : M Unit := do
  match e with
  | .proj _ x | .uproj _ x | .sproj _ _ x | .box _ x | .unbox x | .reset _ x | .isShared x =>
    useVar x
  | .ctor _ ys | .fap _ ys | .pap _ ys =>
    ys.forM useArg
  | .ap x ys | .reuse x _ _ ys =>
    useVar x
    ys.forM useArg
  | .lit _ => pure ()

mutual

private partial def visitFnBody (fnBody : FnBody) (m : JPLiveVarMap) : M Unit := do
  match fnBody with
  | .vdecl x _ v b =>
    visitFnBody b m
    bindVar x
    useExpr v
  | .jdecl j ys v b =>
    visitFnBody b <| updateJPLiveVarMap j ys v m
  | .set x _ y b =>
    visitFnBody b m
    useVar x
    useArg y
  | .uset x _ y b | .sset x _ _ y _ b =>
    visitFnBody b m
    useVar x
    useVar y
  | .setTag x _ b | .inc x _ _ _ b | .dec x _ _ _ b | .del x b =>
    visitFnBody b m
    useVar x
  | .case _ x _ alts =>
    alts.forM (visitFnBody ·.body m)
    useVar x
  | .jmp j ys =>
    visitJP m j
    ys.forM useArg
  | .ret x =>
    useArg x
  | .unreachable => pure ()

partial def updateJPLiveVarMap (j : JoinPointId) (ys : Array Param) (v : FnBody) (m : JPLiveVarMap)
    : JPLiveVarMap :=
  let action : M Unit := do
    visitFnBody v m
    bindParams ys
  let ⟨_, { liveVars }⟩ := action.run {} |>.run
  m.insert j liveVars

end

end LiveVars

def updateLiveVars (e : Expr) (v : LiveVarSet) : LiveVarSet :=
  let ⟨_, { liveVars }⟩ := LiveVars.useExpr e |>.run { liveVars := v }
  liveVars

def collectLiveVars (b : FnBody) (m : JPLiveVarMap) (v : LiveVarSet := {}) : LiveVarSet :=
  let ⟨_, { liveVars }⟩ := LiveVars.visitFnBody b m |>.run { liveVars := v }
  liveVars

export LiveVars (updateJPLiveVarMap)

end Lean.IR
