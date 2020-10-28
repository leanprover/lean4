/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
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
  (env             : Environment)
  (nextMacroScope  : MacroScope    := firstFrontendMacroScope + 1)
  (ngen            : NameGenerator := {})
  (traceState      : TraceState    := {})

instance : Inhabited State := ⟨{ env := arbitrary _ }⟩

structure Context :=
  (options        : Options := {})
  (currRecDepth   : Nat := 0)
  (maxRecDepth    : Nat := 1000)
  (ref            : Syntax := Syntax.missing)

abbrev CoreM := ReaderT Context $ StateRefT State (EIO Exception)

instance {α} : Inhabited (CoreM α) := ⟨fun _ _ => throw $ arbitrary _⟩

instance : Ref CoreM := {
  getRef  := do let ctx ← read; pure ctx.ref,
  withRef := fun ref x => withReader (fun ctx => { ctx with ref := ref }) x
}

instance : MonadEnv CoreM := {
  getEnv    := do pure (← get).env,
  modifyEnv := fun f => modify fun s => { s with env := f s.env }
}

instance : MonadOptions CoreM := {
  getOptions := do pure (← read).options
}

instance : AddMessageContext CoreM := {
  addMessageContext := addMessageContextPartial
}

instance : MonadNameGenerator CoreM := {
  getNGen := do pure (← get).ngen,
  setNGen := fun ngen => modify fun s => { s with ngen := ngen } }

instance : MonadRecDepth CoreM := {
  withRecDepth   := fun d x => withReader (fun ctx => { ctx with currRecDepth := d }) x,
  getRecDepth    := do pure (← read).currRecDepth,
  getMaxRecDepth := do pure (← read).maxRecDepth
}

@[inline] def liftIOCore {α} (x : IO α) : CoreM α := do
  let ref ← getRef
  IO.toEIO (fun (err : IO.Error) => Exception.error ref (toString err)) x

instance : MonadIO CoreM := {
  liftIO := @liftIOCore
}

instance : MonadTrace CoreM := {
  getTraceState    := do pure (← get).traceState,
  modifyTraceState := fun f => modify fun s => { s with traceState := f s.traceState }
}

private def mkFreshNameImp (n : Name) : CoreM Name := do
  let fresh ← modifyGet fun s => (s.nextMacroScope, { s with nextMacroScope := s.nextMacroScope + 1 })
  let env ← getEnv
  pure $ addMacroScope env.mainModule n fresh

def mkFreshUserName {m} [MonadLiftT CoreM m] (n : Name) : m Name :=
  liftM $ mkFreshNameImp n

@[inline] def CoreM.run {α} (x : CoreM α) (ctx : Context) (s : State) : EIO Exception (α × State) :=
  (x ctx).run s

@[inline] def CoreM.run' {α} (x : CoreM α) (ctx : Context) (s : State) : EIO Exception α :=
  Prod.fst <$> x.run ctx s

@[inline] def CoreM.toIO {α} (x : CoreM α) (ctx : Context) (s : State) : IO (α × State) := do
  match (← (x.run ctx s).toIO') with
  | Except.error (Exception.error _ msg) => do let e ← msg.toString; throw $ IO.userError e
  | Except.error (Exception.internal id) => throw $ IO.userError $ "internal exception #" ++ toString id.idx
  | Except.ok a => pure a

instance {α} [MetaEval α] : MetaEval (CoreM α) := {
  eval := fun env opts x _ => do
    let x : CoreM α := do try x finally printTraces
    let (a, s) ← x.toIO { maxRecDepth := getMaxRecDepth opts, options := opts } { env := env }
    MetaEval.eval s.env opts a (hideUnit := true)
}

end Core

export Core (CoreM mkFreshUserName)

@[inline] def catchInternalId {α} {m : Type → Type} [Monad m] [MonadExcept Exception m] (id : InternalExceptionId) (x : m α) (h : Exception → m α) : m α := do
  try
    x
  catch ex => match ex with
    | Exception.error _ _    => throw ex
    | Exception.internal id' => if id == id' then h ex else throw ex

@[inline] def catchInternalIds {α} {m : Type → Type} [Monad m] [MonadExcept Exception m] (ids : List InternalExceptionId) (x : m α) (h : Exception → m α) : m α := do
  try
    x
  catch ex => match ex with
    | Exception.error _ _   => throw ex
    | Exception.internal id => if ids.contains id then h ex else throw ex

end Lean
