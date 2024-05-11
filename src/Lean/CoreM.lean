/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Util.RecDepth
import Lean.Util.Trace
import Lean.Log
import Lean.Eval
import Lean.ResolveName
import Lean.Elab.InfoTree.Types
import Lean.MonadEnv

namespace Lean
register_builtin_option diagnostics : Bool := {
  defValue := false
  group    := "diagnostics"
  descr    := "collect diagnostic information"
}

register_builtin_option diagnostics.threshold : Nat := {
  defValue := 20
  group    := "diagnostics"
  descr    := "only diagnostic counters above this threshold are reported by the definitional equality"
}

register_builtin_option maxHeartbeats : Nat := {
  defValue := 200000
  descr := "maximum amount of heartbeats per command. A heartbeat is number of (small) memory allocations (in thousands), 0 means no limit"
}

namespace Core

builtin_initialize registerTraceClass `Kernel

def getMaxHeartbeats (opts : Options) : Nat :=
  maxHeartbeats.get opts * 1000

abbrev InstantiateLevelCache := PersistentHashMap Name (List Level × Expr)

/-- Cache for the `CoreM` monad -/
structure Cache where
  instLevelType  : InstantiateLevelCache := {}
  instLevelValue : InstantiateLevelCache := {}
  deriving Inhabited

/-- State for the CoreM monad. -/
structure State where
  /-- Current environment. -/
  env             : Environment
  /-- Next macro scope. We use macro scopes to avoid accidental name capture. -/
  nextMacroScope  : MacroScope     := firstFrontendMacroScope + 1
  /-- Name generator for producing unique `FVarId`s, `MVarId`s, and `LMVarId`s -/
  ngen            : NameGenerator  := {}
  /-- Trace messages -/
  traceState      : TraceState     := {}
  /-- Cache for instantiating universe polymorphic declarations. -/
  cache           : Cache          := {}
  /-- Message log. -/
  messages        : MessageLog     := {}
  /-- Info tree. We have the info tree here because we want to update it while adding attributes. -/
  infoState       : Elab.InfoState := {}
  deriving Nonempty

/-- Context for the CoreM monad. -/
structure Context where
  /-- Name of the file being compiled. -/
  fileName       : String
  /-- Auxiliary datastructure for converting `String.Pos` into Line/Column number. -/
  fileMap        : FileMap
  options        : Options := {}
  currRecDepth   : Nat := 0
  maxRecDepth    : Nat := 1000
  ref            : Syntax := Syntax.missing
  currNamespace  : Name := Name.anonymous
  openDecls      : List OpenDecl := []
  initHeartbeats : Nat := 0
  maxHeartbeats  : Nat := getMaxHeartbeats options
  currMacroScope : MacroScope := firstFrontendMacroScope
  /--
  If `diag := true`, different parts of the system collect diagnostics.
  Use the `set_option diag true` to set it to true.
  -/
  diag           : Bool := false
  deriving Nonempty

/-- CoreM is a monad for manipulating the Lean environment.
It is the base monad for `MetaM`.
The main features it provides are:
- name generator state
- environment state
- Lean options context
- the current open namespace
-/
abbrev CoreM := ReaderT Context <| StateRefT State (EIO Exception)

-- Make the compiler generate specialized `pure`/`bind` so we do not have to optimize through the
-- whole monad stack at every use site. May eventually be covered by `deriving`.
@[always_inline]
instance : Monad CoreM := let i := inferInstanceAs (Monad CoreM); { pure := i.pure, bind := i.bind }

instance : Inhabited (CoreM α) where
  default := fun _ _ => throw default

instance : MonadRef CoreM where
  getRef := return (← read).ref
  withRef ref x := withReader (fun ctx => { ctx with ref := ref }) x

instance : MonadEnv CoreM where
  getEnv := return (← get).env
  modifyEnv f := modify fun s => { s with env := f s.env, cache := {} }

instance : MonadOptions CoreM where
  getOptions := return (← read).options

instance : MonadWithOptions CoreM where
  withOptions f x := do
    let options := f (← read).options
    let diag := diagnostics.get options
    if Kernel.isDiagnosticsEnabled (← getEnv) != diag then
      modifyEnv fun env => Kernel.enableDiag env diag
    withReader
      (fun ctx =>
        { ctx with
          options
          diag
          maxRecDepth := maxRecDepth.get options })
      x

-- Helper function for ensuring fields that depend on `options` have the correct value.
@[inline] private def withConsistentCtx (x : CoreM α) : CoreM α := do
  withOptions id x

instance : AddMessageContext CoreM where
  addMessageContext := addMessageContextPartial

instance : MonadNameGenerator CoreM where
  getNGen := return (← get).ngen
  setNGen ngen := modify fun s => { s with ngen := ngen }

instance : MonadRecDepth CoreM where
  withRecDepth d x := withReader (fun ctx => { ctx with currRecDepth := d }) x
  getRecDepth := return (← read).currRecDepth
  getMaxRecDepth := return (← read).maxRecDepth

instance : MonadResolveName CoreM where
  getCurrNamespace := return (← read).currNamespace
  getOpenDecls := return (← read).openDecls

protected def withFreshMacroScope (x : CoreM α) : CoreM α := do
  let fresh ← modifyGetThe Core.State (fun st => (st.nextMacroScope, { st with nextMacroScope := st.nextMacroScope + 1 }))
  withReader (fun ctx => { ctx with currMacroScope := fresh }) x

instance : MonadQuotation CoreM where
  getCurrMacroScope   := return (← read).currMacroScope
  getMainModule       := return (← get).env.mainModule
  withFreshMacroScope := Core.withFreshMacroScope

instance : Elab.MonadInfoTree CoreM where
  getInfoState      := return (← get).infoState
  modifyInfoState f := modify fun s => { s with infoState := f s.infoState }

@[inline] def modifyCache (f : Cache → Cache) : CoreM Unit :=
  modify fun ⟨env, next, ngen, trace, cache, messages, infoState⟩ => ⟨env, next, ngen, trace, f cache, messages, infoState⟩

@[inline] def modifyInstLevelTypeCache (f : InstantiateLevelCache → InstantiateLevelCache) : CoreM Unit :=
  modifyCache fun ⟨c₁, c₂⟩ => ⟨f c₁, c₂⟩

@[inline] def modifyInstLevelValueCache (f : InstantiateLevelCache → InstantiateLevelCache) : CoreM Unit :=
  modifyCache fun ⟨c₁, c₂⟩ => ⟨c₁, f c₂⟩

def instantiateTypeLevelParams (c : ConstantInfo) (us : List Level) : CoreM Expr := do
  if let some (us', r) := (← get).cache.instLevelType.find? c.name then
    if us == us' then
      return r
  let r := c.instantiateTypeLevelParams us
  modifyInstLevelTypeCache fun s => s.insert c.name (us, r)
  return r

def instantiateValueLevelParams (c : ConstantInfo) (us : List Level) : CoreM Expr := do
  if let some (us', r) := (← get).cache.instLevelValue.find? c.name then
    if us == us' then
      return r
  unless c.hasValue do
    throwError "Not a definition or theorem: {c.name}"
  let r := c.instantiateValueLevelParams! us
  modifyInstLevelValueCache fun s => s.insert c.name (us, r)
  return r

@[inline] def liftIOCore (x : IO α) : CoreM α := do
  let ref ← getRef
  IO.toEIO (fun (err : IO.Error) => Exception.error ref (toString err)) x

instance : MonadLift IO CoreM where
  monadLift := liftIOCore

instance : MonadTrace CoreM where
  getTraceState := return (← get).traceState
  modifyTraceState f := modify fun s => { s with traceState := f s.traceState }

/-- Restore backtrackable parts of the state. -/
def restore (b : State) : CoreM Unit :=
  modify fun s => { s with env := b.env, messages := b.messages, infoState := b.infoState }

/--
Restores full state including sources for unique identifiers. Only intended for incremental reuse
between elaboration runs, not for backtracking within a single run.
-/
def restoreFull (b : State) : CoreM Unit :=
  set b

private def mkFreshNameImp (n : Name) : CoreM Name := do
  let fresh ← modifyGet fun s => (s.nextMacroScope, { s with nextMacroScope := s.nextMacroScope + 1 })
  return addMacroScope (← getEnv).mainModule n fresh

def mkFreshUserName (n : Name) : CoreM Name :=
  mkFreshNameImp n

@[inline] def CoreM.run (x : CoreM α) (ctx : Context) (s : State) : EIO Exception (α × State) :=
  ((withConsistentCtx x) ctx).run s

@[inline] def CoreM.run' (x : CoreM α) (ctx : Context) (s : State) : EIO Exception α :=
  Prod.fst <$> x.run ctx s

@[inline] def CoreM.toIO (x : CoreM α) (ctx : Context) (s : State) : IO (α × State) := do
  match (← (x.run { ctx with initHeartbeats := (← IO.getNumHeartbeats) } s).toIO') with
  | Except.error (Exception.error _ msg)   => throw <| IO.userError (← msg.toString)
  | Except.error (Exception.internal id _) => throw <| IO.userError <| "internal exception #" ++ toString id.idx
  | Except.ok a                            => return a

instance [MetaEval α] : MetaEval (CoreM α) where
  eval env opts x _ := do
    let x : CoreM α := do try x finally printTraces
    let (a, s) ← (withConsistentCtx x).toIO { fileName := "<CoreM>", fileMap := default, options := opts } { env := env }
    MetaEval.eval s.env opts a (hideUnit := true)

-- withIncRecDepth for a monad `m` such that `[MonadControlT CoreM n]`
protected def withIncRecDepth [Monad m] [MonadControlT CoreM m] (x : m α) : m α :=
  controlAt CoreM fun runInBase => withIncRecDepth (runInBase x)

@[inline] def checkInterrupted : CoreM Unit := do
  if (← IO.checkCanceled) then
    -- should never be visible to users!
    throw <| Exception.error .missing "elaboration interrupted"

register_builtin_option debug.moduleNameAtTimeout : Bool := {
  defValue := true
  group    := "debug"
  descr    := "include module name in deterministic timeout error messages.\nRemark: we set this option to false to increase the stability of our test suite"
}

def throwMaxHeartbeat (moduleName : Name) (optionName : Name) (max : Nat) : CoreM Unit := do
  let includeModuleName := debug.moduleNameAtTimeout.get (← getOptions)
  let atModuleName := if includeModuleName then s!" at `{moduleName}`" else ""
  let msg := s!"(deterministic) timeout{atModuleName}, maximum number of heartbeats ({max/1000}) has been reached\nuse `set_option {optionName} <num>` to set the limit\nuse `set_option {diagnostics.name} true` to get diagnostic information"
  throw <| Exception.error (← getRef) (MessageData.ofFormat (Std.Format.text msg))

def checkMaxHeartbeatsCore (moduleName : String) (optionName : Name) (max : Nat) : CoreM Unit := do
  unless max == 0 do
    let numHeartbeats ← IO.getNumHeartbeats
    if numHeartbeats - (← read).initHeartbeats > max then
      throwMaxHeartbeat (.mkSimple moduleName) optionName max

def checkMaxHeartbeats (moduleName : String) : CoreM Unit := do
  checkMaxHeartbeatsCore moduleName `maxHeartbeats (← read).maxHeartbeats

def checkSystem (moduleName : String) : CoreM Unit := do
  -- TODO: bring back more checks from the C++ implementation
  checkInterrupted
  checkMaxHeartbeats moduleName

private def withCurrHeartbeatsImp (x : CoreM α) : CoreM α := do
  let heartbeats ← IO.getNumHeartbeats
  withReader (fun ctx => { ctx with initHeartbeats := heartbeats }) x

def withCurrHeartbeats [Monad m] [MonadControlT CoreM m] (x : m α) : m α :=
  controlAt CoreM fun runInBase => withCurrHeartbeatsImp (runInBase x)

def setMessageLog (messages : MessageLog) : CoreM Unit :=
  modify fun s => { s with messages := messages }

def resetMessageLog : CoreM Unit :=
  setMessageLog {}

def getMessageLog : CoreM MessageLog :=
  return (← get).messages

/--
Returns the current log and then resets its messages but does NOT reset `MessageLog.hadErrors`. Used
for incremental reporting during elaboration of a single command.
-/
def getAndEmptyMessageLog : CoreM MessageLog :=
  modifyGet fun log => ({ log with msgs := {} }, log)

instance : MonadLog CoreM where
  getRef      := getRef
  getFileMap  := return (← read).fileMap
  getFileName := return (← read).fileName
  hasErrors   := return (← get).messages.hasErrors
  logMessage msg := do
    let ctx ← read
    let msg := { msg with data := MessageData.withNamingContext { currNamespace := ctx.currNamespace, openDecls := ctx.openDecls } msg.data };
    modify fun s => { s with messages := s.messages.add msg }

end Core

export Core (CoreM mkFreshUserName checkSystem withCurrHeartbeats)

@[inline] def withAtLeastMaxRecDepth [MonadFunctorT CoreM m] (max : Nat) : m α → m α :=
  monadMap (m := CoreM) <| withReader (fun ctx => { ctx with maxRecDepth := Nat.max max ctx.maxRecDepth })

@[inline] def catchInternalId [Monad m] [MonadExcept Exception m] (id : InternalExceptionId) (x : m α) (h : Exception → m α) : m α := do
  try
    x
  catch ex => match ex with
    | .error ..       => throw ex
    | .internal id' _ => if id == id' then h ex else throw ex

@[inline] def catchInternalIds [Monad m] [MonadExcept Exception m] (ids : List InternalExceptionId) (x : m α) (h : Exception → m α) : m α := do
  try
    x
  catch ex => match ex with
    | .error ..      => throw ex
    | .internal id _ => if ids.contains id then h ex else throw ex

/--
  Return true if `ex` was generated by `throwMaxHeartbeat`.
  This function is a bit hackish. The heartbeat exception should probably be an internal exception.
  We used a similar hack at `Exception.isMaxRecDepth` -/
def Exception.isMaxHeartbeat (ex : Exception) : Bool :=
  match ex with
  | Exception.error _ (MessageData.ofFormat (Std.Format.text msg)) => "(deterministic) timeout".isPrefixOf msg
  | _ => false

/-- Creates the expression `d → b` -/
def mkArrow (d b : Expr) : CoreM Expr :=
  return Lean.mkForall (← mkFreshUserName `x) BinderInfo.default d b

/-- Iterated `mkArrow`, creates the expression `a₁ → a₂ → … → aₙ → b`. Also see `arrowDomainsN`. -/
def mkArrowN (ds : Array Expr) (e : Expr) : CoreM Expr := ds.foldrM mkArrow e

private def supportedRecursors :=
  #[``Empty.rec, ``False.rec, ``Eq.ndrec, ``Eq.rec, ``Eq.recOn, ``Eq.casesOn, ``False.casesOn, ``Empty.casesOn, ``And.rec, ``And.casesOn]

/-- This is a temporary workaround for generating better error messages for the compiler. It can be deleted after we
   rewrite the remaining parts of the compiler in Lean.  -/
private def checkUnsupported [Monad m] [MonadEnv m] [MonadError m] (decl : Declaration) : m Unit := do
  let env ← getEnv
  decl.forExprM fun e =>
    let unsupportedRecursor? := e.find? fun
      | Expr.const declName .. =>
        ((isAuxRecursor env declName && !isCasesOnRecursor env declName) || isRecCore env declName)
        && !supportedRecursors.contains declName
      | _ => false
    match unsupportedRecursor? with
    | some (Expr.const declName ..) => throwError "code generator does not support recursor '{declName}' yet, consider using 'match ... with' and/or structural recursion"
    | _ => pure ()

register_builtin_option compiler.enableNew : Bool := {
  defValue := false
  group    := "compiler"
  descr    := "(compiler) enable the new code generator, this should have no significant effect on your code but it does help to test the new code generator; unset to only use the old code generator instead"
}

-- Forward declaration
@[extern "lean_lcnf_compile_decls"]
opaque compileDeclsNew (declNames : List Name) : CoreM Unit

def compileDecl (decl : Declaration) : CoreM Unit := do
  let opts ← getOptions
  let decls := Compiler.getDeclNamesForCodeGen decl
  if compiler.enableNew.get opts then
    compileDeclsNew decls
  let res ← withTraceNode `compiler (fun _ => return m!"compiling old: {decls}") do
    return (← getEnv).compileDecl opts decl
  match res with
  | Except.ok env => setEnv env
  | Except.error (KernelException.other msg) =>
    checkUnsupported decl -- Generate nicer error message for unsupported recursors and axioms
    throwError msg
  | Except.error ex =>
    throwKernelException ex

def compileDecls (decls : List Name) : CoreM Unit := do
  let opts ← getOptions
  if compiler.enableNew.get opts then
    compileDeclsNew decls
  match (← getEnv).compileDecls opts decls with
  | Except.ok env   => setEnv env
  | Except.error (KernelException.other msg) =>
    throwError msg
  | Except.error ex =>
    throwKernelException ex

def getDiag (opts : Options) : Bool :=
  diagnostics.get opts

/-- Return `true` if diagnostic information collection is enabled. -/
def isDiagnosticsEnabled : CoreM Bool :=
  return (← read).diag

def ImportM.runCoreM (x : CoreM α) : ImportM α := do
  let ctx ← read
  let (a, _) ← (withOptions (fun _ => ctx.opts) x).toIO { fileName := "<ImportM>", fileMap := default } { env := ctx.env }
  return a

/-- Return `true` if the exception was generated by one our resource limits. -/
def Exception.isRuntime (ex : Exception) : Bool :=
  ex.isMaxHeartbeat || ex.isMaxRecDepth

/--
Custom `try-catch` for all monads based on `CoreM`. We don't want to catch "runtime exceptions"
in these monads, but on `CommandElabM`. See issues #2775 and #2744 as well as `MonadAlwayExcept`.
-/
@[inline] protected def Core.tryCatch (x : CoreM α) (h : Exception → CoreM α) : CoreM α := do
  try
    x
  catch ex =>
    if ex.isRuntime then
      throw ex -- We should use `tryCatchRuntimeEx` for catching runtime exceptions
    else
      h ex

@[inline] protected def Core.tryCatchRuntimeEx (x : CoreM α) (h : Exception → CoreM α) : CoreM α := do
  try
    x
  catch ex =>
    h ex

instance : MonadExceptOf Exception CoreM where
  throw    := throw
  tryCatch := Core.tryCatch

class MonadRuntimeException (m : Type → Type) where
  tryCatchRuntimeEx (body : m α) (handler : Exception → m α) : m α

export MonadRuntimeException (tryCatchRuntimeEx)

instance : MonadRuntimeException CoreM where
  tryCatchRuntimeEx := Core.tryCatchRuntimeEx

@[inline] instance [MonadRuntimeException m] : MonadRuntimeException (ReaderT ρ m) where
  tryCatchRuntimeEx := fun x c r => tryCatchRuntimeEx (x r) (fun e => (c e) r)

@[inline] instance [MonadRuntimeException m] : MonadRuntimeException (StateRefT' ω σ m) where
  tryCatchRuntimeEx := fun x c s => tryCatchRuntimeEx (x s) (fun e => c e s)

@[inline] def mapCoreM [MonadControlT CoreM m] [Monad m] (f : forall {α}, CoreM α → CoreM α) {α} (x : m α) : m α :=
  controlAt CoreM fun runInBase => f <| runInBase x

end Lean
