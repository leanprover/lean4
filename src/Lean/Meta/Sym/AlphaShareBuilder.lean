/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.SymM
public section
namespace Lean.Meta.Sym.Internal
/-!
Helper functions for constructing maximally shared expressions from maximally shared expressions.
That is, `mkAppS f a` assumes that `f` and `a` are maximally shared.

These functions are in the `Internal` namespace because they can be easily misused.
We use them to construct safe functions.
-/
class MonadShareCommon (m : Type → Type) where
  share1 : Expr → m Expr
  assertShared : Expr → m Unit
  isDebugEnabled : m Bool

@[always_inline]
instance (m n) [MonadLift m n] [MonadShareCommon m] : MonadShareCommon n where
  share1 e := liftM (MonadShareCommon.share1 e : m Expr)
  assertShared e := liftM (MonadShareCommon.assertShared e : m Unit)
  isDebugEnabled := liftM (MonadShareCommon.isDebugEnabled : m Bool)

private def dummy : AlphaKey := { expr := mkConst `__dummy__}

protected def Sym.share1 (e : Expr) : SymM Expr := do
  let prev := (← get).share.set.findD { expr := e } dummy
  if isSameExpr prev.expr dummy.expr then
    -- `e` is new
    modify fun s => { s with share.set := s.share.set.insert { expr := e } }
    return e
  else
    return prev.expr

protected def Sym.assertShared (e : Expr) : SymM Unit := do
  let prev := (← get).share.set.findD { expr := e } dummy
  assert! isSameExpr prev.expr e

instance : MonadShareCommon SymM where
  share1 := Sym.share1
  assertShared := Sym.assertShared
  isDebugEnabled := isDebugEnabled

/--
Helper monad for constructing maximally shared terms.
The `Bool` flag indicates whether it is debug-mode or not.
-/
abbrev AlphaShareBuilderM := ReaderT Bool AlphaShareCommonM

/--
Helper function for lifting a `AlphaShareBuilderM` action to `GrindM`
-/
abbrev liftBuilderM (k : AlphaShareBuilderM α) : SymM α := do
  let share ← modifyGet fun s => (s.share, { s with share := {} })
  let (a, share) := k (← isDebugEnabled) share
  modify fun s => { s with share }
  return a

protected def Builder.share1 (e : Expr) : AlphaShareBuilderM Expr := do
  let prev := (← get).set.findD { expr := e } dummy
  if isSameExpr prev.expr dummy.expr then
    -- `e` is new
    modify fun { set := set } => { set := set.insert { expr := e } }
    return e
  else
    return prev.expr

protected def Builder.assertShared (e : Expr) : AlphaShareBuilderM Unit := do
  assert! (← get).set.contains ⟨e⟩

instance : MonadShareCommon AlphaShareBuilderM where
  share1 := Builder.share1
  assertShared := Builder.assertShared
  isDebugEnabled := read

open MonadShareCommon (share1 assertShared)

variable [MonadShareCommon m]

def mkLitS (l : Literal) : m Expr :=
  share1 <| .lit l

def mkConstS (declName : Name) (us : List Level := []) : m Expr :=
  share1 <| .const declName us

def mkBVarS (idx : Nat) : m Expr :=
  share1 <| .bvar idx

def mkSortS (u : Level) : m Expr :=
  share1 <| .sort u

def mkFVarS (fvarId : FVarId) : m Expr :=
  share1 <| .fvar fvarId

def mkMVarS (mvarId : MVarId) : m Expr :=
  share1 <| .mvar mvarId

variable [Monad m]

def mkMDataS (d : MData) (e : Expr) : m Expr := do
  if (← MonadShareCommon.isDebugEnabled) then
    assertShared e
  share1 <| .mdata d e

def mkProjS (structName : Name) (idx : Nat) (struct : Expr) : m Expr := do
  if (← MonadShareCommon.isDebugEnabled) then
    assertShared struct
  share1 <| .proj structName idx struct

def mkAppS (f a : Expr) : m Expr := do
  if (← MonadShareCommon.isDebugEnabled) then
    assertShared f
    assertShared a
  share1 <| .app f a

def mkLambdaS (x : Name) (bi : BinderInfo) (t : Expr) (b : Expr) : m Expr := do
  if (← MonadShareCommon.isDebugEnabled) then
    assertShared t
    assertShared b
  share1 <| .lam x t b bi

def mkForallS (x : Name) (bi : BinderInfo) (t : Expr) (b : Expr) : m Expr := do
  if (← MonadShareCommon.isDebugEnabled) then
    assertShared t
    assertShared b
  share1 <| .forallE x t b bi

def mkLetS (x : Name) (t : Expr) (v : Expr) (b : Expr) (nondep : Bool := false) : m Expr := do
  if (← MonadShareCommon.isDebugEnabled) then
    assertShared t
    assertShared v
    assertShared b
  share1 <| .letE x t v b nondep

def mkHaveS (x : Name) (t : Expr) (v : Expr) (b : Expr) : m Expr := do
  if (← MonadShareCommon.isDebugEnabled) then
    assertShared t
    assertShared v
    assertShared b
  share1 <| .letE x t v b true

@[inline] def _root_.Lean.Expr.updateAppS! (e : Expr) (newFn : Expr) (newArg : Expr) : m Expr := do
  let .app fn arg := e | panic! "application expected"
  if isSameExpr fn newFn && isSameExpr arg newArg then return e else mkAppS newFn newArg

@[inline] def _root_.Lean.Expr.updateMDataS! (e : Expr) (newExpr : Expr) : m Expr := do
  let .mdata d a := e | panic! "mdata expected"
  if isSameExpr a newExpr then return e else mkMDataS d newExpr

@[inline] def _root_.Lean.Expr.updateProjS! (e : Expr) (newExpr : Expr) : m Expr := do
  let .proj s i a := e | panic! "proj expected"
  if isSameExpr a newExpr then return e else mkProjS s i newExpr

@[inline] def _root_.Lean.Expr.updateForallS! (e : Expr) (newDomain : Expr) (newBody : Expr) : m Expr := do
  let .forallE n d b bi := e | panic! "forall expected"
  if isSameExpr d newDomain && isSameExpr b newBody then
    return e
  else
    mkForallS n bi newDomain newBody

@[inline] def _root_.Lean.Expr.updateLambdaS! (e : Expr) (newDomain : Expr) (newBody : Expr) : m Expr := do
  let .lam n d b bi := e | panic! "lambda expected"
  if isSameExpr d newDomain && isSameExpr b newBody then
    return e
  else
    mkLambdaS n bi newDomain newBody

@[inline] def _root_.Lean.Expr.updateLetS! (e : Expr) (newType : Expr) (newVal : Expr) (newBody : Expr) : m Expr := do
  let .letE n t v b nondep := e | panic! "let expression expected"
  if isSameExpr t newType && isSameExpr v newVal && isSameExpr b newBody then
    return e
  else
    mkLetS n newType newVal newBody nondep

def mkAppS₂ (f a₁ a₂ : Expr) : m Expr := do
  mkAppS (← mkAppS f a₁) a₂

def mkAppS₃ (f a₁ a₂ a₃ : Expr) : m Expr := do
  mkAppS (← mkAppS₂ f a₁ a₂) a₃

def mkAppS₄ (f a₁ a₂ a₃ a₄ : Expr) : m Expr := do
  mkAppS (← mkAppS₃ f a₁ a₂ a₃) a₄

def mkAppS₅ (f a₁ a₂ a₃ a₄ a₅ : Expr) : m Expr := do
  mkAppS (← mkAppS₄ f a₁ a₂ a₃ a₄) a₅

end Lean.Meta.Sym.Internal
