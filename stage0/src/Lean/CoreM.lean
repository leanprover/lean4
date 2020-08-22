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
import Lean.InternalExceptionId
import Lean.Eval

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

inductive Exception
| error (ref : Syntax) (msg : MessageData)
| internal (id : InternalExceptionId)

def Exception.toMessageData : Exception → MessageData
| Exception.error _ msg => msg
| Exception.internal id => id.toString

def Exception.getRef : Exception → Syntax
| Exception.error ref _ => ref
| Exception.internal _  => Syntax.missing

instance Exception.inhabited : Inhabited Exception := ⟨Exception.error (arbitrary _) (arbitrary _)⟩

abbrev ECoreM (ε : Type) := ReaderT Context $ StateRefT State $ EIO ε
abbrev CoreM := ECoreM Exception

instance CoreM.inhabited {α} : Inhabited (CoreM α) :=
⟨fun _ _ => throw $ arbitrary _⟩

def getRef : CoreM Syntax := do
ctx ← read; pure ctx.ref

@[inline] def liftIOCore {α} (x : IO α) : CoreM α := do
ref ← getRef;
adaptExcept
  (fun (err : IO.Error) => Exception.error ref (toString err))
  (liftM x : ECoreM IO.Error α)

instance : MonadIO CoreM :=
{ liftIO := @liftIOCore }

def addContext (msg : MessageData) : CoreM MessageData := do
ctx ← read;
s   ← get;
pure $ MessageData.withContext { env := s.env, mctx := {}, lctx := {}, opts := ctx.options } msg

def throwError {α} (msg : MessageData) : CoreM α := do
ctx ← read;
msg ← addContext msg;
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

def getOptions : CoreM Options :=  do
ctx ← read; pure ctx.options

def getTraceState : CoreM TraceState := do
s ← get; pure s.traceState

def setTraceState (traceState : TraceState) : CoreM Unit := do
modify fun s => { s with traceState := traceState }

def getNGen : CoreM NameGenerator := do
s ← get; pure s.ngen

def setNGen (ngen : NameGenerator) : CoreM Unit :=
modify fun s => { s with ngen := ngen }

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

instance tracer : SimpleMonadTracerAdapter (CoreM) :=
{ getOptions       := getOptions,
  getTraceState    := getTraceState,
  addContext       := addContext,
  modifyTraceState := fun f => modify $ fun s => { s with traceState := f s.traceState } }

def throwKernelException {α} (ex : KernelException) : CoreM α := do
opts ← getOptions;
throwError $ ex.toMessageData opts

def addDecl (decl : Declaration) : CoreM Unit := do
env ← getEnv;
match env.addDecl decl with
| Except.ok    env => setEnv env
| Except.error ex  => throwKernelException ex

def compileDecl (decl : Declaration) : CoreM Unit := do
env  ← getEnv;
opts ← getOptions;
match env.compileDecl opts decl with
| Except.ok env   => setEnv env
| Except.error ex => throwKernelException ex

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

def printTraces : CoreM Unit := do
traceState ← getTraceState;
traceState.traces.forM $ fun m => liftIO $ IO.println $ format m

def resetTraceState : CoreM Unit :=
modify fun s => { s with traceState := {} }

@[inline] def ECoreM.run {ε α} (x : ECoreM ε α) (ctx : Context) (s : State) : EIO ε (α × State) :=
(x.run ctx).run s

@[inline] def ECoreM.run' {ε α} (x : ECoreM ε α) (ctx : Context) (s : State) : EIO ε α :=
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

export Core (CoreM Exception Exception.error Exception.internal)

@[inline] def catchInternalId {α} {m : Type → Type} [MonadExcept Exception m] (id : InternalExceptionId) (x : m α) (h : Exception → m α) : m α :=
catch x fun ex => match ex with
  | Exception.error _ _    => throw ex
  | Exception.internal id' => if id == id' then h ex else throw ex

@[inline] def catchInternalIds {α} {m : Type → Type} [MonadExcept Exception m] (ids : List InternalExceptionId) (x : m α) (h : Exception → m α) : m α :=
catch x fun ex => match ex with
  | Exception.error _ _   => throw ex
  | Exception.internal id => if ids.contains id then h ex else throw ex

end Lean
