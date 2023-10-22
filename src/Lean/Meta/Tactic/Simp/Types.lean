/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.AppBuilder
import Lean.Meta.CongrTheorems
import Lean.Meta.Tactic.Simp.SimpTheorems
import Lean.Meta.Tactic.Simp.SimpCongrTheorems

namespace Lean.Meta
namespace Simp

structure Result where
  expr           : Expr
  proof?         : Option Expr := none -- If none, proof is assumed to be `refl`
  dischargeDepth : Nat := 0
  deriving Inhabited

abbrev Cache := ExprMap Result

abbrev CongrCache := ExprMap (Option CongrTheorem)

structure Context where
  config         : Config := {}
  simpTheorems   : SimpTheoremsArray := {}
  congrTheorems  : SimpCongrTheorems := {}
  parent?        : Option Expr := none
  dischargeDepth : Nat := 0
  deriving Inhabited

def Context.isDeclToUnfold (ctx : Context) (declName : Name) : Bool :=
  ctx.simpTheorems.isDeclToUnfold declName

def Context.mkDefault : MetaM Context :=
  return { config := {}, simpTheorems := #[(← getSimpTheorems)], congrTheorems := (← getSimpCongrTheorems) }

abbrev UsedSimps := HashMap Origin Nat

structure State where
  cache        : Cache := {}
  congrCache   : CongrCache := {}
  usedTheorems : UsedSimps := {}
  numSteps     : Nat := 0

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

def Step.updateResult : Step → Result → Step
  | Step.visit _, r => Step.visit r
  | Step.done _, r  => Step.done r

structure Methods where
  pre        : Expr → SimpM Step          := fun e => return Step.visit { expr := e }
  post       : Expr → SimpM Step          := fun e => return Step.done { expr := e }
  discharge? : Expr → SimpM (Option Expr) := fun _ => return none
  deriving Inhabited

/- Internal monad -/
abbrev M := ReaderT Methods SimpM

def pre (e : Expr) : M Step := do
  (← read).pre e

def post (e : Expr) : M Step := do
  (← read).post e

def discharge? (e : Expr) : M (Option Expr) := do
  (← read).discharge? e

def getConfig : SimpM Config :=
  return (← read).config

@[inline] def withParent (parent : Expr) (f : M α) : M α :=
  withTheReader Context (fun ctx => { ctx with parent? := parent }) f

def getSimpTheorems : M SimpTheoremsArray :=
  return (← readThe Context).simpTheorems

def getSimpCongrTheorems : M SimpCongrTheorems :=
  return (← readThe Context).congrTheorems

@[inline] def withSimpTheorems (s : SimpTheoremsArray) (x : M α) : M α := do
  let cacheSaved := (← get).cache
  modify fun s => { s with cache := {} }
  try
    withTheReader Context (fun ctx => { ctx with simpTheorems := s }) x
  finally
    modify fun s => { s with cache := cacheSaved }

def recordSimpTheorem (thmId : Origin) : SimpM Unit :=
  modify fun s => if s.usedTheorems.contains thmId then s else
    let n := s.usedTheorems.size
    { s with usedTheorems := s.usedTheorems.insert thmId n }

end Simp

export Simp (SimpM)

end Lean.Meta
