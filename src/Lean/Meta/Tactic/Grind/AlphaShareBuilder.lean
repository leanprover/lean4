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
private def share (e : Expr) : GrindM Expr := do
  let key : AlphaKey := ⟨e⟩
  if let some r := (← get).scState.set.find? key then
    return r.expr
  else
    modify fun s => { s with scState.set := s.scState.set.insert key }
    return e

private def assertShared (e : Expr) : GrindM Unit := do
  assert! (← get).scState.set.contains ⟨e⟩

def mkLitS (l : Literal) : GrindM Expr :=
  share <| .lit l

def mkConstS (declName : Name) (us : List Level := []) : GrindM Expr :=
  share <| .const declName us

def mkBVarS (idx : Nat) : GrindM Expr :=
  share <| .bvar idx

def mkSortS (u : Level) : GrindM Expr :=
  share <| .sort u

def mkFVarS (fvarId : FVarId) : GrindM Expr :=
  share <| .fvar fvarId

def mkMVarS (mvarId : MVarId) : GrindM Expr := do
  share <| .mvar mvarId

def mkMDataS (m : MData) (e : Expr) : GrindM Expr := do
  if (← isDebugEnabled) then
    assertShared e
  share <| .mdata m e

def mkProjS (structName : Name) (idx : Nat) (struct : Expr) : GrindM Expr := do
  if (← isDebugEnabled) then
    assertShared struct
  share <| .proj structName idx struct

def mkAppS (f a : Expr) : GrindM Expr := do
  if (← isDebugEnabled) then
    assertShared f
    assertShared a
  share <| .app f a

def mkLambdaS (x : Name) (bi : BinderInfo) (t : Expr) (b : Expr) : GrindM Expr := do
  if (← isDebugEnabled) then
    assertShared t
    assertShared b
  share <| .lam x t b bi

def mkForallS (x : Name) (bi : BinderInfo) (t : Expr) (b : Expr) : GrindM Expr := do
  if (← isDebugEnabled) then
    assertShared t
    assertShared b
  share <| .forallE x t b bi

def mkLetS (x : Name) (t : Expr) (v : Expr) (b : Expr) (nondep : Bool := false) : GrindM Expr := do
  if (← isDebugEnabled) then
    assertShared t
    assertShared v
    assertShared b
  share <| .letE x t v b nondep

def mkHaveS (x : Name) (t : Expr) (v : Expr) (b : Expr) : GrindM Expr := do
  if (← isDebugEnabled) then
    assertShared t
    assertShared v
    assertShared b
  share <| .letE x t v b true

end Lean.Meta.Grind
