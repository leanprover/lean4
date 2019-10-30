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

/-
This module provides three (mutually dependent) goodies:
1- Weak head normal form computation with support for metavariables and transparency modes.
2- Definitionally equality checking with support for metavariables (aka unification modulo definitional equality).
3- Type inference.
-/

namespace Lean
inductive TransparencyMode
| All | Semireducible | Instances | Reducible | None

structure LocalInstance :=
(className : Name)
(fvar      : Expr)

abbrev LocalInstances := Array LocalInstance

structure UnifierConfig :=
(foApprox           : Bool := false)
(ctxApprox          : Bool := false)
(quasiPatternApprox : Bool := false)

structure TypeInferenceConfig :=
(opts           : Options          := {})
(unifierConfig  : UnifierConfig    := {})
(transparency   : TransparencyMode := TransparencyMode.Semireducible)
(smartUnfolding : Bool             := true)
(useZeta        : Bool             := true)

/- Abstract cache interfact for `TypeInference` functions.
   TODO: add missing methods. -/
class AbstractTypeInferenceCache (ϕ : Type) :=
(getWHNF : ϕ → TransparencyMode → Expr → Option Expr)
(setWHNF : ϕ → TransparencyMode → Expr → Expr → ϕ)

-- TODO: add special cases
inductive TypeInferenceException
| other : String → TypeInferenceException

structure TypeInferenceContext :=
(env            : Environment)
(lctx           : LocalContext)
(localInstances : LocalInstances)
(config         : TypeInferenceConfig := {})

structure TypeInferenceState (σ ϕ : Type) :=
(mctx           : σ)
(cache          : ϕ)
(ngen           : NameGenerator)
(traceState     : TraceState)
(usedAssignment : Bool := false)
(postponed      : Array (Level × Level) := #[])

instance TypeInferenceState.backtrackable {σ ϕ} : EState.Backtrackable σ (TypeInferenceState σ ϕ) :=
{ save    := fun s => s.mctx,
  restore := fun s mctx => { mctx := mctx, .. s } }

/-- Type Context Monad -/
abbrev TypeInferenceM (σ ϕ : Type) := ReaderT TypeInferenceContext (EState TypeInferenceException (TypeInferenceState σ ϕ))

namespace TypeInference
variables {σ ϕ : Type}

private def getOptions : TypeInferenceM σ ϕ Options :=
do ctx ← read; pure ctx.config.opts

private def getTraceState : TypeInferenceM σ ϕ TraceState :=
do s ← get; pure s.traceState

instance tracer : SimpleMonadTracerAdapter (TypeInferenceM σ ϕ) :=
{ getOptions       := getOptions,
  getTraceState    := getTraceState,
  modifyTraceState := fun f => modify $ fun s => { traceState := f s.traceState, .. s } }

end TypeInference

inductive TypeInferenceNoCache
| mk

instance typeContextNoCacheIsAbstractTCCache : AbstractTypeInferenceCache TypeInferenceNoCache :=
{ getWHNF := fun _ _ _ => none,
  setWHNF := fun s _ _ _ => s }

end Lean
