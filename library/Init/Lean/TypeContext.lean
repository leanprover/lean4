/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Control.Reader
import Init.Lean.NameGenerator
import Init.Lean.Environment
import Init.Lean.AbstractMetavarContext
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

/-- Abstract Type Context Monad -/
abbrev ATCM (σ ϕ : Type) := ReaderT TCContext (EState TCException (TCState σ ϕ))

namespace AbstractTypeContext
variables {σ ϕ : Type}

private def getOptions : ATCM σ ϕ Options :=
do ctx ← read; pure ctx.config.opts

private def getTraceState : ATCM σ ϕ TraceState :=
do s ← get; pure s.traceState

instance tracer : SimpleMonadTracerAdapter (ATCM σ ϕ) :=
{ getOptions       := getOptions,
  getTraceState    := getTraceState,
  modifyTraceState := fun f => modify $ fun s => { traceState := f s.traceState, .. s } }

end AbstractTypeContext

inductive TypeContextNoCache
| mk

instance typeContextNoCacheIsAbstractTCCache : AbstractTCCache TypeContextNoCache :=
{ getWHNF := fun _ _ _ => none,
  setWHNF := fun s _ _ _ => s
}

end Lean
