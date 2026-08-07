/-
Copyright (c) 2019 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich
-/
module

prelude
public import Init.Data.OfScientific
public import Lean.Data.Options

public section

namespace Lean

register_builtin_option profiler : Bool := {
  defValue := false
  descr    := "show exclusive execution times of various Lean components

See also `trace.profiler` for an alternative profiling system with structured output."
}

register_builtin_option profiler.threshold : Nat := {
  defValue := 100
  descr    := "threshold in milliseconds, profiling times under threshold will not be reported individually"
}

@[export lean_get_profiler]
private def get_profiler (o : Options) : Bool :=
  profiler.get o

@[export lean_get_profiler_threshold]
def profiler.threshold.getSecs (o : Options) : Float :=
  (profiler.threshold.get o).toFloat / 1000

/-- Print and accumulate run time of `act` when option `profiler` is set to `true`. -/
@[extern "lean_profileit"]
def profileit {α : Type} (category : @& String) (opts : @& Options) (fn : Unit → α) (decl := Name.anonymous) : α := fn ()

unsafe def profileitIOUnsafe {ε α : Type} (category : String) (opts : Options) (act : EIO ε α) (decl := Name.anonymous) : EIO ε α :=
  match profileit (decl := decl) category opts fun _ => unsafeEIO act with
  | Except.ok a    => pure a
  | Except.error e => throw e

@[implemented_by profileitIOUnsafe]
def profileitIO {ε α : Type} (category : String) (opts : Options) (act : EIO ε α) (decl := Name.anonymous) : EIO ε α := act

-- impossible to infer `ε`
def profileitM {m : Type → Type} (ε : Type) [MonadFunctorT (EIO ε) m] {α : Type} (category : String) (opts : Options) (act : m α) (decl := Name.anonymous) : m α :=
  monadMap (fun {β} => profileitIO (ε := ε) (α := β) (decl := decl) category opts) act

/-- Print all profiling times (if any) to standard error. -/
@[extern "lean_display_cumulative_profiling_times"]
opaque displayCumulativeProfilingTimes : BaseIO Unit

/-!
## Per-declaration heartbeat costs

The heartbeat counter is maintained unconditionally by the allocator for `maxHeartbeats`, so
attributing it to declarations costs only two counter reads and an array push per declaration and
phase. Collection is always on: compiling a module writes the costs to `<module>.hb.json` next to
the `.olean`, the way `.ilean` files are always produced. Unlike `trace.profiler`, the data is
`O(declarations)` rather than `O(trace nodes)`, which is what makes this affordable by default.
-/

/-- Heartbeats used by one phase of processing one declaration. -/
structure HeartbeatEntry where
  /--
  User-written declaration the cost rolls up to. Auxiliary declarations (matchers, equation
  lemmas, generated code, `deriving`-generated instances) report the declaration that caused them.
  Declarations compiled as one mutual clique share the clique's first declaration as the owner of
  that shared work, while their elaboration is attributed individually.
  -/
  owner : Name
  /-- Declaration the heartbeats were actually spent on, e.g. an auxiliary of `owner`. -/
  declName : Name
  /-- Phase that used the heartbeats; `elab` or `kernel`. -/
  phase : Name
  /-- Raw heartbeats, i.e. `IO.getNumHeartbeats` units. Divide by 1000 for the `maxHeartbeats` unit. -/
  heartbeats : Nat
  deriving Inhabited

/--
Attribution state for per-declaration heartbeat costs; see `Core.withCostOwner`.
-/
inductive CostOwner where
  /-- No owner established. -/
  | unknown
  /--
  The command elaborator's best-effort approximation of the declaration name, to be refined once
  by the first declaration elaborator that knows the elaborated name.
  -/
  | pending (declName : Name)
  /--
  The owner is decided; nested machine-generated elaboration stays attributed to it.
  -/
  | fixed (declName : Name)
  deriving Inhabited

/-- The owner's declaration name, if one is established. -/
def CostOwner.name? : CostOwner → Option Name
  | .unknown => none
  | .pending declName | .fixed declName => some declName

end Lean
