/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.AppBuilder
import Lean.Meta.Tactic.Simp.SimpLemmas
import Lean.Meta.Tactic.Simp.CongrLemmas

namespace Lean.Meta
namespace Simp

structure Result where
  expr   : Expr
  proof? : Option Expr := none -- If none, proof is assumed to be `refl`
  deriving Inhabited

abbrev Cache := ExprMap Result

structure Context where
  config         : Config      := {}
  simpLemmas     : SimpLemmas  := {}
  congrLemmas    : CongrLemmas := {}
  parent?        : Option Expr := none
  dischargeDepth : Nat      := 0
  deriving Inhabited

def Context.mkDefault : MetaM Context :=
  return { config := {}, simpLemmas := (← getSimpLemmas), congrLemmas := (← getCongrLemmas) }

structure State where
  cache    : Cache := {}
  numSteps : Nat := 0

abbrev SimpM := ReaderT Context $ StateRefT State MetaM

instance : MonadBacktrack SavedState SimpM where
  saveState      := Meta.saveState
  restoreState s := s.restore

inductive Step where
  | visit : Result → Step
  | done  : Result → Step
  deriving Inhabited

def Step.result : Step → Result
  | Step.visit r => r
  | Step.done r => r

structure Methods where
  pre        : Expr → SimpM Step          := fun e => return Step.visit { expr := e }
  post       : Expr → SimpM Step          := fun e => return Step.done { expr := e }
  discharge? : Expr → SimpM (Option Expr) := fun e => return none
  deriving Inhabited

/- Internal monad -/
abbrev M := ReaderT Methods SimpM

def pre (e : Expr) : M Step := do
  (← read).pre e

def post (e : Expr) : M Step := do
  (← read).post e

def discharge? (e : Expr) : M (Option Expr) := do
  (← read).discharge? e

def getConfig : M Config :=
  return (← readThe Context).config

@[inline] def withParent (parent : Expr) (f : M α) : M α :=
  withTheReader Context (fun ctx => { ctx with parent? := parent }) f

def getSimpLemmas : M SimpLemmas :=
  return (← readThe Context).simpLemmas

def getCongrLemmas : M CongrLemmas :=
  return (← readThe Context).congrLemmas

@[inline] def withSimpLemmas (s : SimpLemmas) (x : M α) : M α := do
  let cacheSaved := (← get).cache
  modify fun s => { s with cache := {} }
  try
    withTheReader Context (fun ctx => { ctx with simpLemmas := s }) x
  finally
    modify fun s => { s with cache := cacheSaved }

end Simp

export Simp (SimpM)

end Lean.Meta
