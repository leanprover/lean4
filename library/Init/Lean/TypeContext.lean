/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Control.Reader
import Init.Lean.NameGenerator
import Init.Lean.Environment
import Init.Lean.LocalContext
import Init.Lean.Trace

namespace Lean
inductive TransparencyMode
| All | Semireducible | Instances | Reducible | None

structure LocalInstance :=
(className : Name)
(fvar      : Expr)

abbrev LocalInstances := Array LocalInstance

structure UnifierOptions :=
(foApprox           : Bool := false)
(ctxApprox          : Bool := false)
(quasiPatternApprox : Bool := false)

structure TCOptions :=
(opts           : Options          := {})
(unifierConfig  : UnifierOptions   := {})
(transparency   : TransparencyMode := TransparencyMode.Semireducible)
(smartUnfolding : Bool             := true)
(useZeta        : Bool             := true)

/- We can `TypeContext` functions with different implementations of
   metavariable contexts.  For elaboration and tactic framework, we
   use `MetavarContext`.  During type class resolution and simplifier,
   we use temporary metavariables which are cheaper to create and
   dispose. Moreover, given a particular task using temporary
   metavariables (e.g., matching the left-hand side of an equation),
   we assume all metavariables share the same local context.
   If `sharedContext == false`, then support for "delayed assignments" is
   required. -/
class AbstractMetavarContext (σ : Type) :=
(isLevelMVar {}     : Level → Bool)
(getLevelAssignment (mctx : σ) (mvarId : Name) : Option Level)
(assignLevel        (mctx : σ) (mvarId : Name) (val : Level) : σ)
(isExprMVar {}      : Expr → Bool)
(getExprAssignment  (mctx : σ) (mvarId : Name) : Option Expr)
(assignExpr         (mctx : σ) (mvarId : Name) (val : Expr) : σ)
(getExprMVarContext (mctx : σ) (mvarId : Name) : Option LocalContext)
(sharedContext      : Bool)
(isDelayedAssigned  (mctx : σ) (mvarId : Name) : Bool)
(assignDelayed      (mctx : σ) (mvarId : Name) (lctx : LocalContext) (fvars : List Expr) (val : Expr) : σ)

/- Abstract cache interfact for `TypeContext` functions.
   TODO: add missing methods. -/
class AbstractTCCache (ϕ : Type) :=
(getWHNF : ϕ → TransparencyMode → Expr → Option Expr)
(setWHNF : ϕ → TransparencyMode → Expr → Expr → ϕ)

-- TODO: add special cases
inductive TCException
| other : String → TCException

structure TCContext :=
(env            : Environment)
(lctx           : LocalContext)
(localInstances : LocalInstances)
(config         : TCOptions := {})

structure TCState (σ ϕ : Type) :=
(mctx           : σ)
(cache          : ϕ)
(ngen           : NameGenerator)
(traceState     : TraceState)
(usedAssignment : Bool := false)
(postponed      : Array (Level × Level) := #[])

instance TCState.backtrackable {σ ϕ} : EState.Backtrackable σ (TCState σ ϕ) :=
{ save    := fun s => s.mctx,
  restore := fun s mctx => { mctx := mctx, .. s } }

abbrev TypeContextM (σ ϕ : Type) := ReaderT TCContext (EState TCException (TCState σ ϕ))

namespace TypeContext

variables {σ ϕ : Type}

private def getOptions : TypeContextM σ ϕ Options :=
do ctx ← read; pure ctx.config.opts

private def getTraceState : TypeContextM σ ϕ TraceState :=
do s ← get; pure s.traceState

instance tracer : SimpleMonadTracerAdapter (TypeContextM σ ϕ) :=
{ getOptions       := getOptions,
  getTraceState    := getTraceState,
  modifyTraceState := fun f => modify $ fun s => { traceState := f s.traceState, .. s } }

end TypeContext

end Lean
