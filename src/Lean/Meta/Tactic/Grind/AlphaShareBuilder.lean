/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
public section
namespace Lean.Meta.Grind
/-!
Helper functions for constructing maximally shared expressions from maximally shared expressions.
-/
protected def Grind.share (e : Expr) : GrindM Expr := do
  let key : AlphaKey := ⟨e⟩
  if let some r := (← get).scState.set.find? key then
    return r.expr
  else
    modify fun s => { s with scState.set := s.scState.set.insert key }
    return e

protected def Grind.assertShared (e : Expr) : GrindM Unit := do
  assert! (← get).scState.set.contains ⟨e⟩

class MonadShareCommon (m : Type → Type) where
  share : Expr → m Expr
  assertShared : Expr → m Unit
  isDebugEnabled : m Bool

@[always_inline]
instance (m n) [MonadLift m n] [MonadShareCommon m] : MonadShareCommon n where
  share e := liftM (MonadShareCommon.share e : m Expr)
  assertShared e := liftM (MonadShareCommon.assertShared e : m Unit)
  isDebugEnabled := liftM (MonadShareCommon.isDebugEnabled : m Bool)

instance : MonadShareCommon GrindM where
  share := Grind.share
  assertShared := Grind.assertShared
  isDebugEnabled := isDebugEnabled

/--
Helper monad for constructing maximally shared terms.
The `Bool` flag indicates whether it is debug-mode or not.
-/
abbrev AlphaShareBuilderM := ReaderT Bool AlphaShareCommonM

/--
Helper function for lifting a `AlphaShareBuilderM` action to `GrindM`
-/
abbrev liftBuilderM (k : AlphaShareBuilderM α) : GrindM α := do
  let scState ← modifyGet fun s => (s.scState, { s with scState := {} })
  let (a, scState) := k (← isDebugEnabled) scState
  modify fun s => { s with scState }
  return a

protected def Builder.share (e : Expr) : AlphaShareBuilderM Expr := do
  let key : AlphaKey := ⟨e⟩
  if let some r := (← get).set.find? key then
    return r.expr
  else
    modify fun s => { s with set := s.set.insert key }
    return e

protected def Builder.assertShared (e : Expr) : AlphaShareBuilderM Unit := do
  assert! (← get).set.contains ⟨e⟩

instance : MonadShareCommon AlphaShareBuilderM where
  share := Builder.share
  assertShared := Builder.assertShared
  isDebugEnabled := read

open MonadShareCommon (share assertShared)

variable [MonadShareCommon m]

def mkLitS (l : Literal) : m Expr :=
  share <| .lit l

def mkConstS (declName : Name) (us : List Level := []) : m Expr :=
  share <| .const declName us

def mkBVarS (idx : Nat) : m Expr :=
  share <| .bvar idx

def mkSortS (u : Level) : m Expr :=
  share <| .sort u

def mkFVarS (fvarId : FVarId) : m Expr :=
  share <| .fvar fvarId

def mkMVarS (mvarId : MVarId) : m Expr :=
  share <| .mvar mvarId

variable [Monad m]

def mkMDataS (d : MData) (e : Expr) : m Expr := do
  if (← MonadShareCommon.isDebugEnabled) then
    assertShared e
  share <| .mdata d e

def mkProjS (structName : Name) (idx : Nat) (struct : Expr) : m Expr := do
  if (← MonadShareCommon.isDebugEnabled) then
    assertShared struct
  share <| .proj structName idx struct

def mkAppS (f a : Expr) : m Expr := do
  if (← MonadShareCommon.isDebugEnabled) then
    assertShared f
    assertShared a
  share <| .app f a

def mkLambdaS (x : Name) (bi : BinderInfo) (t : Expr) (b : Expr) : m Expr := do
  if (← MonadShareCommon.isDebugEnabled) then
    assertShared t
    assertShared b
  share <| .lam x t b bi

def mkForallS (x : Name) (bi : BinderInfo) (t : Expr) (b : Expr) : m Expr := do
  if (← MonadShareCommon.isDebugEnabled) then
    assertShared t
    assertShared b
  share <| .forallE x t b bi

def mkLetS (x : Name) (t : Expr) (v : Expr) (b : Expr) (nondep : Bool := false) : m Expr := do
  if (← MonadShareCommon.isDebugEnabled) then
    assertShared t
    assertShared v
    assertShared b
  share <| .letE x t v b nondep

def mkHaveS (x : Name) (t : Expr) (v : Expr) (b : Expr) : m Expr := do
  if (← MonadShareCommon.isDebugEnabled) then
    assertShared t
    assertShared v
    assertShared b
  share <| .letE x t v b true

end Lean.Meta.Grind
