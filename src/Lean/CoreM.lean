/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Init.System.IO
import Init.Control.StateRef
import Lean.Util.RecDepth
import Lean.Util.Trace
import Lean.Environment
import Lean.Exception
import Lean.InternalExceptionId
import Lean.Eval
import Lean.MonadEnv

namespace Lean
namespace Core

structure State :=
(env         : Environment)
(ngen        : NameGenerator := {})
(traceState  : TraceState    := {})

instance State.inhabited : Inhabited State := ⟨{ env := arbitrary _ }⟩

structure Context :=
(options        : Options := {})
(currRecDepth   : Nat := 0)
(maxRecDepth    : Nat := 1000)
(ref            : Syntax := Syntax.missing)

abbrev CoreM := ReaderT Context $ StateRefT State $ EIO Exception

instance CoreM.inhabited {α} : Inhabited (CoreM α) :=
⟨fun _ _ => throw $ arbitrary _⟩

instance : MonadError CoreM :=
{ getRef     := do ctx ← read; pure ctx.ref,
  addContext := fun ref msg => do
    ctx ← read;
    s   ← get;
    pure (ref, MessageData.withContext { env := s.env, mctx := {}, lctx := {}, opts := ctx.options } msg) }

instance : MonadEnv CoreM :=
{ getEnv    := do s ← get; pure s.env,
  modifyEnv := fun f => modify fun s => { s with env := f s.env } }

instance : MonadOptions CoreM :=
{ getOptions := do ctx ← read; pure ctx.options }

instance : MonadNameGenerator CoreM :=
{ getNGen := do s ← get; pure s.ngen,
  setNGen := fun ngen => modify fun s => { s with ngen := ngen } }

@[inline] def liftIOCore {α} (x : IO α) : CoreM α := do
ref ← getRef;
liftM $ (adaptExcept (fun (err : IO.Error) => Exception.error ref (toString err)) x : EIO Exception α)

instance : MonadIO CoreM :=
{ liftIO := @liftIOCore }

def checkRecDepth : CoreM Unit := do
ctx ← read;
when (ctx.currRecDepth == ctx.maxRecDepth) $ throwError maxRecDepthErrorMessage

def Context.incCurrRecDepth (ctx : Context) : Context :=
{ ctx with currRecDepth := ctx.currRecDepth + 1 }

@[inline] def withIncRecDepth {α} (x : CoreM α) : CoreM α := do
checkRecDepth; adaptReader Context.incCurrRecDepth x

def Context.replaceRef (ref : Syntax) (ctx : Context) : Context :=
{ ctx with ref := replaceRef ref ctx.ref }

@[inline] def withRef {α} (ref : Syntax) (x : CoreM α) : CoreM α := do
adaptReader (Context.replaceRef ref) x

instance tracer : SimpleMonadTracerAdapter (CoreM) :=
{ getOptions       := getOptions,
  getTraceState    := do s ← get; pure s.traceState,
  addTraceContext  := fun msg => Prod.snd <$> addContext Syntax.missing msg,
  modifyTraceState := fun f => modify $ fun s => { s with traceState := f s.traceState } }

@[inline] def CoreM.run {α} (x : CoreM α) (ctx : Context) (s : State) : EIO Exception (α × State) :=
(x.run ctx).run s

@[inline] def CoreM.run' {α} (x : CoreM α) (ctx : Context) (s : State) : EIO Exception α :=
Prod.fst <$> x.run ctx s

@[inline] def CoreM.toIO {α} (x : CoreM α) (ctx : Context) (s : State) : IO (α × State) :=
adaptExcept
  (fun (ex : Exception) => match ex with
    | Exception.error _ msg => IO.userError $ toString $ format msg
    | Exception.internal id => IO.userError $ toString $ "internal exception #" ++ toString id.idx)
  (x.run ctx s)

instance hasEval {α} [MetaHasEval α] : MetaHasEval (CoreM α) :=
⟨fun env opts x _ => do
   (a, s) ← (finally x printTraces).toIO { maxRecDepth := getMaxRecDepth opts, options := opts} { env := env};
   MetaHasEval.eval s.env opts a⟩

end Core

export Core (CoreM)

@[inline] def catchInternalId {α} {m : Type → Type} [MonadExcept Exception m] (id : InternalExceptionId) (x : m α) (h : Exception → m α) : m α :=
catch x fun ex => match ex with
  | Exception.error _ _    => throw ex
  | Exception.internal id' => if id == id' then h ex else throw ex

@[inline] def catchInternalIds {α} {m : Type → Type} [MonadExcept Exception m] (ids : List InternalExceptionId) (x : m α) (h : Exception → m α) : m α :=
catch x fun ex => match ex with
  | Exception.error _ _   => throw ex
  | Exception.internal id => if ids.contains id then h ex else throw ex

end Lean
