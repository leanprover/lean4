/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Simp.SimpLemmas

namespace Lean.Meta
namespace Simp

def defaultMaxSteps := 100000

structure Result where
  expr   : Expr
  proof? : Option Expr := none -- If none, proof is assumed to be `refl`

abbrev Cache := ExprMap Result

structure Config where
  maxSteps   : Nat  := defaultMaxSteps
  contextual : Bool := false
  memoize    : Bool := true
  singlePass : Bool := false
  zeta       : Bool := true
  beta       : Bool := true
  eta        : Bool := true
  proj       : Bool := true
  ctorEq     : Bool := true

structure Context where
  config     : Config
  parent?    : Option Expr := none
  simpLemmas : SimpLemmas

structure State (σ : Type) where
  user     : σ -- user state
  cache    : Cache := {}
  numSteps : Nat := 0

abbrev SimpM (σ : Type) := ReaderT Context $ StateRefT (State σ) $ MetaM

inductive Step where
  | visit : Result → Step
  | done  : Result → Step

structure Methods (σ : Type) where
  pre        : Expr → SimpM σ Step          := fun e => return Step.visit { expr := e }
  post       : Expr → SimpM σ Step          := fun e => return Step.done { expr := e }
  discharge? : Expr → SimpM σ (Option Expr) := fun e => return none

/- Internal monad -/
abbrev M (σ : Type) := ReaderT (Methods σ) $ SimpM σ

end Simp

export Simp (SimpM)

end Lean.Meta
