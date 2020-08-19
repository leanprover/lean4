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
(ref            : Syntax := Syntax.missing)

inductive Exception
| io     (ex : IO.Error)
| kernel (ex : KernelException) (opts : Options)
| error  (ref : Syntax) (msg : MessageData)

instance Exception.inhabited : Inhabited Exception := ⟨Exception.error Syntax.missing (arbitrary _)⟩

def Exception.toMessageData : Exception → MessageData
| Exception.io ex          => ex.toString
| Exception.kernel ex opts => ex.toMessageData opts
| Exception.error _ msg    => msg

instance Exception.hasToString : HasToString Exception := ⟨fun ex => toString ex.toMessageData⟩

abbrev ECoreM (ε : Type) := ReaderT Context $ StateRefT State $ EIO ε

abbrev CoreM := ECoreM Exception

instance ECoreM.inhabited {ε α} [Inhabited ε] : Inhabited (ECoreM ε α) :=
⟨fun _ _ => throw $ arbitrary _⟩

@[inline] def liftIOCore {α} (x : IO α) : EIO Exception α :=
adaptExcept Exception.io x

instance : MonadIO (EIO Exception) := mkMonadIO @liftIOCore

def throwError {α} (msg : MessageData) : CoreM α := do
ctx ← read;
throw $ Exception.error ctx.ref msg

def ofExcept {ε α} [HasToString ε] (x : Except ε α) : CoreM α :=
match x with
| Except.ok a    => pure a
| Except.error e => throwError $ toString e

def checkRecDepth : CoreM Unit := do
ctx ← read;
when (ctx.currRecDepth == ctx.maxRecDepth) $ throwError maxRecDepthErrorMessage

def Context.incCurrRecDepth (ctx : Context) : Context :=
{ ctx with currRecDepth := ctx.currRecDepth + 1 }

@[inline] def withIncRecDepth {α} (x : CoreM α) : CoreM α := do
checkRecDepth; adaptReader Context.incCurrRecDepth x

def getEnv : CoreM Environment := do
s ← get; pure s.env

def setEnv (env : Environment) : CoreM Unit :=
modify $ fun s => { s with env := env }

@[inline] def modifyEnv (f : Environment → Environment) : CoreM Unit :=
modify $ fun s => { s with env := f s.env }

def getOptions {ε} : ECoreM ε Options :=  do
ctx ← read; pure ctx.options

def getTraceState {ε} [MonadIO (EIO ε)] : ECoreM ε TraceState := do
s ← get; pure s.traceState

def mkFreshId : CoreM Name := do
s ← get;
let id := s.ngen.curr;
modify $ fun s => { s with ngen := s.ngen.next };
pure id

def replaceRef (ref : Syntax) (oldRef : Syntax) : Syntax :=
match ref.getPos with
| some _ => ref
| _      => oldRef

def Context.replaceRef (ref : Syntax) (ctx : Context) : Context :=
{ ctx with ref := replaceRef ref ctx.ref }

@[inline] def withRef {α} (ref : Syntax) (x : CoreM α) : CoreM α := do
adaptReader (Context.replaceRef ref) x

@[inline] private def getTraceState : CoreM TraceState := do
s ← get; pure s.traceState

def addContext {ε} [MonadIO (EIO ε)] (msg : MessageData) : ECoreM ε MessageData := do
ctx ← read;
s   ← get;
pure $ MessageData.withContext { env := s.env, mctx := {}, lctx := {}, opts := ctx.options } msg

instance tracer {ε} [MonadIO (EIO ε)]  : SimpleMonadTracerAdapter (ECoreM ε) :=
{ getOptions       := getOptions,
  getTraceState    := getTraceState,
  addContext       := addContext,
  modifyTraceState := fun f => modify $ fun s => { s with traceState := f s.traceState } }

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
let x : CoreM (Environment × α) := finally (do a ← x; env ← getEnv; pure (env, a)) do {
  traceState ← getTraceState;
  traceState.traces.forM $ fun m => liftIO $ IO.println $ format m
};
let x : EIO Exception (Environment × α) := (x { maxRecDepth := getMaxRecDepth options, options := options }).run' { env := env };
x.toIO fun ex => match ex with
    | Exception.io ex         => ex
    | Exception.kernel ex opt => IO.userError $ toString $ format $ ex.toMessageData opt
    | Exception.error _ msg   => IO.userError $ toString $ format $ msg

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
