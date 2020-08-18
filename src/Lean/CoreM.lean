/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Init.System.IO
import Lean.Util.RecDepth
import Lean.Util.Trace
import Lean.Environment
import Lean.Eval

namespace Lean
namespace Core

structure State :=
(env         : Environment)
(ngen        : NameGenerator := {})
(traceState  : TraceState    := {})

structure Context :=
(options        : Options := {})
(currRecDepth   : Nat := 0)
(maxRecDepth    : Nat)
(stateRef       : IO.Ref State)
(ref            : Syntax := Syntax.missing)

inductive Exception
| io (ex : IO.Error)
| kernel (ex : KernelException) (opts : Options)
| error (ref : Syntax) (msg : MessageData)

abbrev CoreM := ReaderT Context $ EIO Exception

@[inline] def withIncRecDepth {α} (x : CoreM α) : CoreM α := do
ctx ← read;
when (ctx.currRecDepth == ctx.maxRecDepth) $ throw $ Exception.error Syntax.missing maxRecDepthErrorMessage;
adaptReader (fun (ctx : Context) => { ctx with currRecDepth := ctx.currRecDepth + 1 }) x

@[inline] def liftIOCore {α} (x : IO α) : EIO Exception α :=
EIO.adaptExcept Exception.io x

@[inline] def liftIO {α} (x : IO α) : CoreM α :=
fun _ => liftIOCore x

instance monadIO : MonadIO CoreM :=
mkMonadIO @liftIO {
  throw := fun α ex => throw $ Exception.io ex,
  catch := fun α x handler => catch x (fun ex => match ex with
    | Exception.io ex => handler ex
    | ex => throw ex)
}

instance monadExcept : MonadExceptOf Exception CoreM :=
inferInstance

private def getState : CoreM State :=
fun ctx => liftIOCore ctx.stateRef.get

private def setState (s : State) : CoreM Unit :=
fun ctx => liftIOCore $ ctx.stateRef.set s

@[inline] private def modifyGetState {α} (f : State → α × State) : CoreM α := do
s ← getState; let (a, s) := f s; setState s; pure a

instance monadState : MonadState State CoreM :=
{ get       := getState,
  set       := setState,
  modifyGet := @modifyGetState }

def getEnv : CoreM Environment := do
s ← get; pure s.env

def setEnv (env : Environment) : CoreM Unit :=
modify $ fun s => { s with env := env }

def getOptions : CoreM Options :=  do
ctx ← read; pure ctx.options

def getTraceState : CoreM TraceState := do
s ← get; pure s.traceState

def replaceRef (ref : Syntax) (oldRef : Syntax) : Syntax :=
match ref.getPos with
| some _ => ref
| _      => oldRef

@[inline] def withRef {α} (ref : Syntax) (x : CoreM α) : CoreM α := do
adaptReader (fun (ctx : Context) => { ctx with ref := replaceRef ref ctx.ref }) x

@[inline] private def getTraceState : CoreM TraceState := do
s ← get; pure s.traceState

def addContext (msg : MessageData) : CoreM MessageData := do
ctx ← read;
s   ← get;
pure $ MessageData.withContext { env := s.env, mctx := {}, lctx := {}, opts := ctx.options } msg

instance tracer : SimpleMonadTracerAdapter CoreM :=
{ getOptions       := getOptions,
  getTraceState    := getTraceState,
  addContext       := addContext,
  modifyTraceState := fun f => modify $ fun s => { s with traceState := f s.traceState } }

def throwError {α} (msg : MessageData) : CoreM α := do
ctx ← read;
throw $ Exception.error ctx.ref msg

def addDecl (decl : Declaration) : CoreM Unit := do
env ← getEnv;
match env.addDecl decl with
| Except.ok    env => setEnv env
| Except.error ex  => do opts ← getOptions; throw $ Exception.kernel ex opts

def compileDecl (decl : Declaration) : CoreM Unit := do
env  ← getEnv;
opts ← getOptions;
match env.compileDecl opts decl with
| Except.ok env   => setEnv env
| Except.error ex => do opts ← getOptions; throw $ Exception.kernel ex opts

def addAndCompile (decl : Declaration) : CoreM Unit := do
addDecl decl;
compileDecl decl

def dbgTrace {α} [HasToString α] (a : α) : CoreM Unit :=
_root_.dbgTrace (toString a) $ fun _ => pure ()

def getConstInfo (constName : Name) : CoreM ConstantInfo := do
env ← getEnv;
match env.find? constName with
| some info => pure info
| none      => throwError ("unknown constant '" ++ constName ++ "'")

@[inline] def runCore {α} (x : CoreM α) (env : Environment) (options : Options := {}) : IO (Environment × α) := do
ref ← IO.mkRef { env := env : State };
let x : CoreM (Environment × α) := finally (do a ← x; pure (env, a)) do {
  traceState ← getTraceState;
  traceState.traces.forM $ fun m => liftIO $ IO.println $ format m
};
let x : EIO Exception (Environment × α) := x { maxRecDepth := getMaxRecDepth options, options := options, stateRef := ref };
EIO.adaptExcept
  (fun ex => match ex with
    | Exception.io ex         => ex
    | Exception.kernel ex opt => IO.userError $ toString $ format $ ex.toMessageData opt
    | Exception.error _ msg   => IO.userError $ toString $ format $ msg)
  x

@[inline] def run {α} (x : CoreM α) (env : Environment) (options : Options := {}) : IO α := do
(_, a) ← runCore x env options;
pure a

instance hasEval {α} [MetaHasEval α] : MetaHasEval (CoreM α) :=
⟨fun env opts x _ => do
  (env, a) ← runCore x env opts;
  MetaHasEval.eval env opts a⟩

end Core

export Core (CoreM)

end Lean
