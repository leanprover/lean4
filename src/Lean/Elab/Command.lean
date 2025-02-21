/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Gabriel Ebner
-/
prelude
import Lean.Meta.Diagnostics
import Lean.Elab.Binders
import Lean.Elab.SyntheticMVars
import Lean.Elab.SetOption
import Lean.Language.Basic

namespace Lean.Elab.Command

/--
A `Scope` records the part of the `CommandElabM` state that respects scoping,
such as the data for `universe`, `open`, and `variable` declarations, the current namespace,
and currently enabled options.
The `CommandElabM` state contains a stack of scopes, and only the top `Scope`
on the stack is read from or modified. There is always at least one `Scope` on the stack,
even outside any `section` or `namespace`, and each new pushed `Scope`
starts as a modified copy of the previous top scope.
-/
structure Scope where
  /--
  The component of the `namespace` or `section` that this scope is associated to.
  For example, `section a.b.c` and `namespace a.b.c` each create three scopes with headers
  named `a`, `b`, and `c`.
  This is used for checking the `end` command. The "base scope" has `""` as its header.
  -/
  header        : String
  /--
  The current state of all set options at this point in the scope. Note that this is the
  full current set of options and does *not* simply contain the options set
  while this scope has been active.
  -/
  opts          : Options := {}
  /-- The current namespace. The top-level namespace is represented by `Name.anonymous`. -/
  currNamespace : Name := Name.anonymous
  /-- All currently `open`ed namespaces and names. -/
  openDecls     : List OpenDecl := []
  /-- The current list of names for universe level variables to use for new declarations. This is managed by the `universe` command. -/
  levelNames    : List Name := []
  /--
  The current list of binders to use for new declarations.
  This is managed by the `variable` command.
  Each binder is represented in `Syntax` form, and it is re-elaborated
  within each command that uses this information.

  This is also used by commands, such as `#check`, to create an initial local context,
  even if they do not work with binders per se.
  -/
  varDecls      : Array (TSyntax ``Parser.Term.bracketedBinder) := #[]
  /--
  Globally unique internal identifiers for the `varDecls`.
  There is one identifier per variable introduced by the binders
  (recall that a binder such as `(a b c : Ty)` can produce more than one variable),
  and each identifier is the user-provided variable name with a macro scope.
  This is used by `TermElabM` in `Lean.Elab.Term.Context` to help with processing macros
  that capture these variables.
  -/
  varUIds       : Array Name := #[]
  /-- `include`d section variable names (from `varUIds`) -/
  includedVars  : List Name := []
  /-- `omit`ted section variable names (from `varUIds`) -/
  omittedVars  : List Name := []
  /--
  If true (default: false), all declarations that fail to compile
  automatically receive the `noncomputable` modifier.
  A scope with this flag set is created by `noncomputable section`.

  Recall that a new scope inherits all values from its parent scope,
  so all sections and namespaces nested within a `noncomputable` section also have this flag set.
  -/
  isNoncomputable : Bool := false
  deriving Inhabited

structure State where
  env            : Environment
  messages       : MessageLog := {}
  scopes         : List Scope := [{ header := "" }]
  nextMacroScope : Nat := firstFrontendMacroScope + 1
  maxRecDepth    : Nat
  ngen           : NameGenerator := {}
  infoState      : InfoState := {}
  traceState     : TraceState := {}
  snapshotTasks  : Array (Language.SnapshotTask Language.SnapshotTree) := #[]
  deriving Nonempty

structure Context where
  fileName       : String
  fileMap        : FileMap
  currRecDepth   : Nat := 0
  cmdPos         : String.Pos := 0
  macroStack     : MacroStack := []
  currMacroScope : MacroScope := firstFrontendMacroScope
  ref            : Syntax := Syntax.missing
  /--
  Snapshot for incremental reuse and reporting of command elaboration. Currently only used for
  (mutual) defs and contained tactics, in which case the `DynamicSnapshot` is a
  `HeadersParsedSnapshot`.

  Definitely resolved in `Lean.Elab.Command.elabCommandTopLevel`.

  Invariant: if the bundle's `old?` is set, the context and state at the beginning of current and
  old elaboration are identical.
  -/
  snap?          : Option (Language.SnapshotBundle Language.DynamicSnapshot)
  /-- Cancellation token forwarded to `Core.cancelTk?`. -/
  cancelTk?      : Option IO.CancelToken
  /--
  If set (when `showPartialSyntaxErrors` is not set and parsing failed), suppresses most elaboration
  errors; see also `logMessage` below.
  -/
  suppressElabErrors : Bool := false

abbrev CommandElabM := ReaderT Context $ StateRefT State $ EIO Exception
abbrev CommandElab  := Syntax → CommandElabM Unit
structure Linter where
  run : Syntax → CommandElabM Unit
  name : Name := by exact decl_name%

/-
Make the compiler generate specialized `pure`/`bind` so we do not have to optimize through the
whole monad stack at every use site. May eventually be covered by `deriving`.

Remark: see comment at TermElabM
-/
@[always_inline]
instance : Monad CommandElabM := let i := inferInstanceAs (Monad CommandElabM); { pure := i.pure, bind := i.bind }

/--
Like `Core.tryCatchRuntimeEx`; runtime errors are generally used to abort term elaboration, so we do
want to catch and process them at the command level.
-/
@[inline] protected def tryCatch (x : CommandElabM α) (h : Exception → CommandElabM α) :
    CommandElabM α := do
  try
    x
  catch ex =>
    if ex.isInterrupt then
      throw ex
    else
      h ex

instance : MonadExceptOf Exception CommandElabM where
  throw    := throw
  tryCatch := Command.tryCatch

def mkState (env : Environment) (messages : MessageLog := {}) (opts : Options := {}) : State := {
  env         := env
  messages    := messages
  scopes      := [{ header := "", opts := opts }]
  maxRecDepth := maxRecDepth.get opts
}

/- Linters should be loadable as plugins, so store in a global IO ref instead of an attribute managed by the
    environment (which only contains `import`ed objects). -/
builtin_initialize lintersRef : IO.Ref (Array Linter) ← IO.mkRef #[]
builtin_initialize registerTraceClass `Elab.lint

def addLinter (l : Linter) : IO Unit := do
  let ls ← lintersRef.get
  lintersRef.set (ls.push l)

instance : MonadInfoTree CommandElabM where
  getInfoState      := return (← get).infoState
  modifyInfoState f := modify fun s => { s with infoState := f s.infoState }

instance : MonadEnv CommandElabM where
  getEnv := do pure (← get).env
  modifyEnv f := modify fun s => { s with env := f s.env }

@[always_inline]
instance : MonadOptions CommandElabM where
  getOptions := do pure (← get).scopes.head!.opts

protected def getRef : CommandElabM Syntax :=
  return (← read).ref

instance : AddMessageContext CommandElabM where
  addMessageContext := addMessageContextPartial

instance : MonadRef CommandElabM where
  getRef := Command.getRef
  withRef ref x := withReader (fun ctx => { ctx with ref := ref }) x

instance : MonadTrace CommandElabM where
  getTraceState := return (← get).traceState
  modifyTraceState f := modify fun s => { s with traceState := f s.traceState }

instance : AddErrorMessageContext CommandElabM where
  add ref msg := do
    let ctx ← read
    let ref := getBetterRef ref ctx.macroStack
    let msg ← addMessageContext msg
    let msg ← addMacroStack msg ctx.macroStack
    return (ref, msg)

private def runCore (x : CoreM α) : CommandElabM α := do
  let s ← get
  let ctx ← read
  let heartbeats ← IO.getNumHeartbeats
  let env := Kernel.resetDiag s.env
  let scope := s.scopes.head!
  let coreCtx : Core.Context := {
    fileName           := ctx.fileName
    fileMap            := ctx.fileMap
    currRecDepth       := ctx.currRecDepth
    maxRecDepth        := s.maxRecDepth
    ref                := ctx.ref
    currNamespace      := scope.currNamespace
    openDecls          := scope.openDecls
    initHeartbeats     := heartbeats
    currMacroScope     := ctx.currMacroScope
    options            := scope.opts
    cancelTk?          := ctx.cancelTk?
    suppressElabErrors := ctx.suppressElabErrors }
  let x : EIO _ _ := x.run coreCtx {
    env
    ngen := s.ngen
    nextMacroScope := s.nextMacroScope
    infoState.enabled := s.infoState.enabled
    traceState := s.traceState
    snapshotTasks := s.snapshotTasks
  }
  let (ea, coreS) ← liftM x
  modify fun s => { s with
    env               := coreS.env
    nextMacroScope    := coreS.nextMacroScope
    ngen              := coreS.ngen
    infoState.trees   := s.infoState.trees.append coreS.infoState.trees
    traceState.traces := coreS.traceState.traces.map fun t => { t with ref := replaceRef t.ref ctx.ref }
    snapshotTasks     := coreS.snapshotTasks
    messages          := s.messages ++ coreS.messages
  }
  return ea

def liftCoreM (x : CoreM α) : CommandElabM α := do
  MonadExcept.ofExcept (← runCore (observing x))

@[inline] def liftIO {α} (x : IO α) : CommandElabM α := do
  let ctx ← read
  IO.toEIO (fun (ex : IO.Error) => Exception.error ctx.ref ex.toString) x

instance : MonadLiftT IO CommandElabM where
  monadLift := liftIO

/-- Return the current scope. -/
def getScope : CommandElabM Scope := do pure (← get).scopes.head!

instance : MonadResolveName CommandElabM where
  getCurrNamespace := return (← getScope).currNamespace
  getOpenDecls     := return (← getScope).openDecls

instance : MonadLog CommandElabM where
  getRef      := getRef
  getFileMap  := return (← read).fileMap
  getFileName := return (← read).fileName
  hasErrors   := return (← get).messages.hasErrors
  logMessage msg := do
    if (← read).suppressElabErrors then
      -- discard elaboration errors on parse error
      unless msg.data.hasTag (· matches `trace) do
        return
    let currNamespace ← getCurrNamespace
    let openDecls ← getOpenDecls
    let msg := { msg with data := MessageData.withNamingContext { currNamespace := currNamespace, openDecls := openDecls } msg.data }
    modify fun s => { s with messages := s.messages.add msg }

def runLinters (stx : Syntax) : CommandElabM Unit := do
  profileitM Exception "linting" (← getOptions) do
    withTraceNode `Elab.lint (fun _ => return m!"running linters") do
      let linters ← lintersRef.get
      unless linters.isEmpty do
        for linter in linters do
          withTraceNode `Elab.lint (fun _ => return m!"running linter: {.ofConstName linter.name}")
              (tag := linter.name.toString) do
            let savedState ← get
            try
              linter.run stx
            catch ex =>
              match ex with
              | Exception.error ref msg =>
                logException (.error ref m!"linter {.ofConstName linter.name} failed: {msg}")
              | Exception.internal _ _ =>
                logException ex
            finally
              -- TODO: it would be good to preserve even more state (#4363) but preserving info
              -- trees currently breaks from linters adding context-less info nodes
              modify fun s => { savedState with messages := s.messages, traceState := s.traceState }

/--
Catches and logs exceptions occurring in `x`. Unlike `try catch` in `CommandElabM`, this function
catches interrupt exceptions as well and thus is intended for use at the top level of elaboration.
Interrupt and abort exceptions are caught but not logged.
-/
@[inline] def withLoggingExceptions (x : CommandElabM Unit) : CommandElabM Unit := fun ctx ref =>
  EIO.catchExceptions (withLogging x ctx ref) (fun _ => pure ())

@[inherit_doc Core.wrapAsync]
def wrapAsync (act : Unit → CommandElabM α) (cancelTk? : Option IO.CancelToken) :
    CommandElabM (EIO Exception α) := do
  let ctx ← read
  let ctx := { ctx with cancelTk? }
  let st ← get
  return act () |>.run ctx |>.run' st

open Language in
@[inherit_doc Core.wrapAsyncAsSnapshot]
-- `CoreM` and `CommandElabM` are too different to meaningfully share this code
def wrapAsyncAsSnapshot (act : Unit → CommandElabM Unit) (cancelTk? : Option IO.CancelToken)
    (desc : String := by exact decl_name%.toString) :
    CommandElabM (BaseIO SnapshotTree) := do
  let t ← wrapAsync (cancelTk? := cancelTk?) fun _ => do
    IO.FS.withIsolatedStreams (isolateStderr := Core.stderrAsMessages.get (← getOptions)) do
      let tid ← IO.getTID
      -- reset trace state and message log so as not to report them twice
      modify fun st => { st with
        messages := st.messages.markAllReported
        traceState := { tid }
        snapshotTasks := #[]
      }
      try
        withTraceNode `Elab.async (fun _ => return desc) do
          act ()
      catch e =>
        logError e.toMessageData
      finally
        addTraceAsMessages
      get
  let ctx ← read
  return do
    match (← t.toBaseIO) with
    | .ok (output, st) =>
      let mut msgs := st.messages
      if !output.isEmpty then
        msgs := msgs.add {
          fileName := ctx.fileName
          severity := MessageSeverity.information
          pos      := ctx.fileMap.toPosition <| ctx.ref.getPos?.getD 0
          data     := output
        }
      return .mk {
        desc
        diagnostics := (← Language.Snapshot.Diagnostics.ofMessageLog msgs)
        traces := st.traceState
      } st.snapshotTasks
    -- interrupt or abort exception as `try catch` above should have caught any others
    | .error _ => default

@[inherit_doc Core.logSnapshotTask]
def logSnapshotTask (task : Language.SnapshotTask Language.SnapshotTree) : CommandElabM Unit :=
  modify fun s => { s with snapshotTasks := s.snapshotTasks.push task }

def runLintersAsync (stx : Syntax) : CommandElabM Unit := do
  if !Elab.async.get (← getOptions) then
    withoutModifyingEnv do
      runLinters stx
    return

  -- We only start one task for all linters for now as most linters are fast and we simply want
  -- to unblock elaboration of the next command
  let cancelTk ← IO.CancelToken.new
  let lintAct ← wrapAsyncAsSnapshot (cancelTk? := cancelTk) fun _ => runLinters stx
  logSnapshotTask { stx? := none, task := (← BaseIO.asTask lintAct), cancelTk? := cancelTk }

protected def getCurrMacroScope : CommandElabM Nat  := do pure (← read).currMacroScope
protected def getMainModule     : CommandElabM Name := do pure (← getEnv).mainModule

protected def withFreshMacroScope {α} (x : CommandElabM α) : CommandElabM α := do
  let fresh ← modifyGet (fun st => (st.nextMacroScope, { st with nextMacroScope := st.nextMacroScope + 1 }))
  withReader (fun ctx => { ctx with currMacroScope := fresh }) x

instance : MonadQuotation CommandElabM where
  getCurrMacroScope   := Command.getCurrMacroScope
  getMainModule       := Command.getMainModule
  withFreshMacroScope := Command.withFreshMacroScope

unsafe def mkCommandElabAttributeUnsafe (ref : Name) : IO (KeyedDeclsAttribute CommandElab) :=
  mkElabAttribute CommandElab `builtin_command_elab `command_elab `Lean.Parser.Command `Lean.Elab.Command.CommandElab "command" ref

@[implemented_by mkCommandElabAttributeUnsafe]
opaque mkCommandElabAttribute (ref : Name) : IO (KeyedDeclsAttribute CommandElab)

builtin_initialize commandElabAttribute : KeyedDeclsAttribute CommandElab ← mkCommandElabAttribute decl_name%

private def mkInfoTree (elaborator : Name) (stx : Syntax) (trees : PersistentArray InfoTree) : CommandElabM InfoTree := do
  let ctx ← read
  let s ← get
  let scope := s.scopes.head!
  let tree := InfoTree.node (Info.ofCommandInfo { elaborator, stx }) trees
  let ctx := PartialContextInfo.commandCtx {
    env := s.env, fileMap := ctx.fileMap, mctx := {}, currNamespace := scope.currNamespace,
    openDecls := scope.openDecls, options := scope.opts, ngen := s.ngen
  }
  return InfoTree.context ctx tree

/--
Disables incremental command reuse *and* reporting for `act` if `cond` is true by setting
`Context.snap?` to `none`.
-/
def withoutCommandIncrementality (cond : Bool) (act : CommandElabM α) : CommandElabM α := do
  let opts ← getOptions
  withReader (fun ctx => { ctx with snap? := ctx.snap?.filter fun snap => Id.run do
    if let some old := snap.old? then
      if cond && opts.getBool `trace.Elab.reuse then
        dbg_trace "reuse stopped: guard failed at {old.stx}"
    return !cond
  }) act

private def elabCommandUsing (s : State) (stx : Syntax) : List (KeyedDeclsAttribute.AttributeEntry CommandElab) → CommandElabM Unit
  | []                => withInfoTreeContext (mkInfoTree := mkInfoTree `no_elab stx) <| throwError "unexpected syntax{indentD stx}"
  | (elabFn::elabFns) =>
    catchInternalId unsupportedSyntaxExceptionId
      (do
        -- prevent unsupported commands from accidentally accessing `Context.snap?` (e.g. by nested
        -- supported commands)
        withoutCommandIncrementality (!(← isIncrementalElab elabFn.declName)) do
        withInfoTreeContext (mkInfoTree := mkInfoTree elabFn.declName stx) do
         elabFn.value stx)
      (fun _ => do set s; elabCommandUsing s stx elabFns)

/-- Elaborate `x` with `stx` on the macro stack -/
def withMacroExpansion (beforeStx afterStx : Syntax) (x : CommandElabM α) : CommandElabM α :=
  withInfoContext (mkInfo := pure <| .ofMacroExpansionInfo { stx := beforeStx, output := afterStx, lctx := .empty }) do
    withReader (fun ctx => { ctx with macroStack := { before := beforeStx, after := afterStx } :: ctx.macroStack }) x

instance : MonadMacroAdapter CommandElabM where
  getCurrMacroScope := getCurrMacroScope
  getNextMacroScope := return (← get).nextMacroScope
  setNextMacroScope next := modify fun s => { s with nextMacroScope := next }

instance : MonadRecDepth CommandElabM where
  withRecDepth d x := withReader (fun ctx => { ctx with currRecDepth := d }) x
  getRecDepth      := return (← read).currRecDepth
  getMaxRecDepth   := return (← get).maxRecDepth

builtin_initialize registerTraceClass `Elab.command

open Language in
/-- Snapshot after macro expansion of a command. -/
structure MacroExpandedSnapshot extends Snapshot where
  /-- The declaration name of the macro. -/
  macroDecl : Name
  /-- The expanded syntax tree. -/
  newStx    : Syntax
  /-- `State.nextMacroScope` after expansion. -/
  newNextMacroScope : Nat
  /-- Whether any traces were present after expansion. -/
  hasTraces : Bool
  /--
  Follow-up elaboration snapshots, one per command if `newStx` is a sequence of commands.
  -/
  next : Array (SnapshotTask DynamicSnapshot)
deriving TypeName
open Language in
instance : ToSnapshotTree MacroExpandedSnapshot where
  toSnapshotTree s := ⟨s.toSnapshot, s.next.map (·.map (sync := true) toSnapshotTree)⟩

partial def elabCommand (stx : Syntax) : CommandElabM Unit := do
  withLogging <| withRef stx <| withIncRecDepth <| withFreshMacroScope do
    match stx with
    | Syntax.node _ k args =>
      if k == nullKind then
        -- list of commands => elaborate in order
        -- The parser will only ever return a single command at a time, but syntax quotations can return multiple ones
        -- Incrementality is currently limited to the common case where the sequence is the direct
        -- output of a macro, see below.
        withoutCommandIncrementality true do
          args.forM elabCommand
      else withTraceNode `Elab.command (fun _ => return stx) (tag :=
        -- special case: show actual declaration kind for `declaration` commands
        (if stx.isOfKind ``Parser.Command.declaration then stx[1] else stx).getKind.toString) do
        let s ← get
        match (← liftMacroM <| expandMacroImpl? s.env stx) with
        | some (decl, stxNew?) =>
          withInfoTreeContext (mkInfoTree := mkInfoTree decl stx) do
            let stxNew ← liftMacroM <| liftExcept stxNew?
            withMacroExpansion stx stxNew do
              -- Support incrementality; see also Note [Incremental Macros]
              if let some snap := (←read).snap? then
                -- Unpack nested commands; see `MacroExpandedSnapshot.next`
                let cmds := if stxNew.isOfKind nullKind then stxNew.getArgs else #[stxNew]
                let nextMacroScope := (← get).nextMacroScope
                let hasTraces := (← getTraceState).traces.size > 0
                let oldSnap? := do
                  let oldSnap ← snap.old?
                  let oldSnap ← oldSnap.val.get.toTyped? MacroExpandedSnapshot
                  guard <| oldSnap.macroDecl == decl && oldSnap.newNextMacroScope == nextMacroScope
                  -- check absence of traces; see Note [Incremental Macros]
                  guard <| !oldSnap.hasTraces && !hasTraces
                  return oldSnap
                if snap.old?.isSome && oldSnap?.isNone then
                  snap.old?.forM (·.val.cancelRec)
                let oldCmds? := oldSnap?.map fun old =>
                  if old.newStx.isOfKind nullKind then old.newStx.getArgs else #[old.newStx]
                let cmdPromises ← cmds.mapM fun _ => IO.Promise.new
                snap.new.resolve <| .ofTyped {
                  diagnostics := .empty
                  macroDecl := decl
                  newStx := stxNew
                  newNextMacroScope := nextMacroScope
                  hasTraces
                  next := Array.zipWith (fun cmdPromise cmd =>
                    { stx? := some cmd, task := cmdPromise.resultD default }) cmdPromises cmds
                  : MacroExpandedSnapshot
                }
                -- After the first command whose syntax tree changed, we must disable
                -- incremental reuse
                let mut reusedCmds := true
                let opts ← getOptions
                -- For each command, associate it with new promise and old snapshot, if any, and
                -- elaborate recursively
                for cmd in cmds, cmdPromise in cmdPromises, i in [0:cmds.size] do
                  let oldCmd? := oldCmds?.bind (·[i]?)
                  withReader ({ · with snap? := some {
                    new := cmdPromise
                    old? := do
                      guard reusedCmds
                      let old ← oldSnap?
                      return { stx := (← oldCmd?), val := (← old.next[i]?) }
                  } }) do
                    if oldSnap?.isSome && (← read).snap?.isNone then
                      oldSnap?.bind (·.next[i]?) |>.forM (·.cancelRec)
                    elabCommand cmd
                    -- Resolve promise for commands not supporting incrementality; waiting for
                    -- `withAlwaysResolvedPromises` to do this could block reporting by later
                    -- commands
                    cmdPromise.resolve default
                  reusedCmds := reusedCmds && oldCmd?.any (·.eqWithInfoAndTraceReuse opts cmd)
              else
                elabCommand stxNew
        | _ =>
          match commandElabAttribute.getEntries s.env k with
          | []      =>
            withInfoTreeContext (mkInfoTree := mkInfoTree `no_elab stx) <|
              throwError "elaboration function for '{k}' has not been implemented"
          | elabFns => elabCommandUsing s stx elabFns
    | _ =>
      withInfoTreeContext (mkInfoTree := mkInfoTree `no_elab stx) <|
        throwError "unexpected command"

builtin_initialize registerTraceClass `Elab.input

/-- Option for showing elaboration errors from partial syntax errors. -/
register_builtin_option showPartialSyntaxErrors : Bool := {
  defValue := false
  descr    := "show elaboration errors from partial syntax trees (i.e. after parser recovery)"
}

builtin_initialize
  registerTraceClass `Elab.info
  registerTraceClass `Elab.snapshotTree

/--
`elabCommand` wrapper that should be used for the initial invocation, not for recursive calls after
macro expansion etc.
-/
def elabCommandTopLevel (stx : Syntax) : CommandElabM Unit := withRef stx do profileitM Exception "elaboration" (← getOptions) do
  withReader ({ · with suppressElabErrors :=
    stx.hasMissing && !showPartialSyntaxErrors.get (← getOptions) }) do
  let initMsgs ← modifyGet fun st => (st.messages, { st with messages := {} })
  let initInfoTrees ← getResetInfoTrees
  try
    -- We should *not* factor out `elabCommand`'s `withLogging` to here since it would make its error
    -- recovery more coarse. In particular, If `c` in `set_option ... in $c` fails, the remaining
    -- `end` command of the `in` macro would be skipped and the option would be leaked to the outside!
    elabCommand stx
    -- Run the linters, unless `#guard_msgs` is present, which is special and runs `elabCommandTopLevel` itself,
    -- so it is a "super-top-level" command. This is the only command that does this, so we just special case it here
    -- rather than engineer a general solution.
    unless (stx.find? (·.isOfKind ``Lean.guardMsgsCmd)).isSome do
      withLogging do
        runLintersAsync stx
  finally
    -- Make sure `snap?` is definitely resolved; we do not use it for reporting as `#guard_msgs` may
    -- be the caller of this function and add new messages and info trees
    if let some snap := (← read).snap? then
      snap.new.resolve default

    -- note the order: first process current messages & info trees, then add back old messages & trees,
    -- then convert new traces to messages
    let mut msgs := (← get).messages
    for tree in (← getInfoTrees) do
      trace[Elab.info] (← tree.format)
    modify fun st => { st with
      messages := initMsgs ++ msgs
      infoState := { st.infoState with trees := initInfoTrees ++ st.infoState.trees }
    }
    addTraceAsMessages

/-- Adapt a syntax transformation to a regular, command-producing elaborator. -/
def adaptExpander (exp : Syntax → CommandElabM Syntax) : CommandElab := fun stx => do
  let stx' ← exp stx
  withMacroExpansion stx stx' <| elabCommand stx'

private def getVarDecls (s : State) : Array Syntax :=
  s.scopes.head!.varDecls

instance {α} : Inhabited (CommandElabM α) where
  default := throw default

/--
The environment linter framework needs to be able to run linters with the same context
as `liftTermElabM`, so we expose that context as a public function here.
-/
def mkMetaContext : Meta.Context := {
  config := { foApprox := true, ctxApprox := true, quasiPatternApprox := true }
}

open Lean.Parser.Term in
/-- Return identifier names in the given bracketed binder. -/
def getBracketedBinderIds : Syntax → CommandElabM (Array Name)
  | `(bracketedBinderF|($ids* $[: $ty?]? $(_annot?)?)) => return ids.map Syntax.getId
  | `(bracketedBinderF|{$ids* $[: $ty?]?})             => return ids.map Syntax.getId
  | `(bracketedBinderF|⦃$ids* : $_⦄)                   => return ids.map Syntax.getId
  | `(bracketedBinderF|[$id : $_])                     => return #[id.getId]
  | `(bracketedBinderF|[$_])                           => return #[Name.anonymous]
  | _                                                  => throwUnsupportedSyntax

private def mkTermContext (ctx : Context) (s : State) : CommandElabM Term.Context := do
  let scope      := s.scopes.head!
  let mut sectionVars := {}
  for id in (← scope.varDecls.flatMapM getBracketedBinderIds), uid in scope.varUIds do
    sectionVars := sectionVars.insert id uid
  return {
    macroStack             := ctx.macroStack
    sectionVars            := sectionVars
    isNoncomputableSection := scope.isNoncomputable }

/--
Lift the `TermElabM` monadic action `x` into a `CommandElabM` monadic action.

Note that `x` is executed with an empty message log. Thus, `x` cannot modify/view messages produced by
previous commands.

If you need to access the free variables corresponding to the ones declared using the `variable` command,
consider using `runTermElabM`.

Recall that `TermElabM` actions can automatically lift `MetaM` and `CoreM` actions.
Example:
```
import Lean

open Lean Elab Command Meta

def printExpr (e : Expr) : MetaM Unit := do
  IO.println s!"{← ppExpr e} : {← ppExpr (← inferType e)}"

#eval
  liftTermElabM do
    printExpr (mkConst ``Nat)
```
-/
def liftTermElabM (x : TermElabM α) : CommandElabM α := do
  let ctx ← read
  let s   ← get
  -- dbg_trace "heartbeats: {heartbeats}"
  let scope := s.scopes.head!
  -- We execute `x` with an empty message log. Thus, `x` cannot modify/view messages produced by previous commands.
  -- This is useful for implementing `runTermElabM` where we use `Term.resetMessageLog`
  let x : TermElabM _  := withSaveInfoContext x
  -- make sure `observing` below also catches runtime exceptions (like we do by default in
  -- `CommandElabM`)
  let _ := MonadAlwaysExcept.except (m := TermElabM)
  let x : MetaM _ := (observing (try x finally Meta.reportDiag)).run (← mkTermContext ctx s) { levelNames := scope.levelNames }
  let x : CoreM _ := x.run mkMetaContext {}
  let ((ea, _), _) ← runCore x
  MonadExcept.ofExcept ea

instance : MonadEval TermElabM CommandElabM where
  monadEval := liftTermElabM

/--
Execute the monadic action `elabFn xs` as a `CommandElabM` monadic action, where `xs` are free variables
corresponding to all active scoped variables declared using the `variable` command.

This method is similar to `liftTermElabM`, but it elaborates all scoped variables declared using the `variable`
command.

Example:
```
import Lean

open Lean Elab Command Meta

variable {α : Type u} {f : α → α}
variable (n : Nat)

#eval
  runTermElabM fun xs => do
    for x in xs do
      IO.println s!"{← ppExpr x} : {← ppExpr (← inferType x)}"
```
-/
def runTermElabM (elabFn : Array Expr → TermElabM α) : CommandElabM α := do
  let scope ← getScope
  liftTermElabM <|
    Term.withAutoBoundImplicit <|
      Term.elabBinders scope.varDecls fun xs => do
        -- We need to synthesize postponed terms because this is a checkpoint for the auto-bound implicit feature
        -- If we don't use this checkpoint here, then auto-bound implicits in the postponed terms will not be handled correctly.
        Term.synthesizeSyntheticMVarsNoPostponing
        let mut sectionFVars := {}
        for uid in scope.varUIds, x in xs do
          sectionFVars := sectionFVars.insert uid x
        withReader ({ · with sectionFVars := sectionFVars }) do
          -- We don't want to store messages produced when elaborating `(getVarDecls s)` because they have already been saved when we elaborated the `variable`(s) command.
          -- So, we use `Core.resetMessageLog`.
          Core.resetMessageLog
          let someType := mkSort levelZero
          Term.addAutoBoundImplicits' xs someType fun xs _ =>
            Term.withoutAutoBoundImplicit <| elabFn xs

private def liftAttrM {α} (x : AttrM α) : CommandElabM α := do
  liftCoreM x

/--
Return the stack of all currently active scopes:
the base scope always comes last; new scopes are prepended in the front.
In particular, the current scope is always the first element.
-/
def getScopes : CommandElabM (List Scope) := do
  pure (← get).scopes

def modifyScope (f : Scope → Scope) : CommandElabM Unit :=
  modify fun s => { s with
    scopes := match s.scopes with
      | h::t => f h :: t
      | []   => unreachable!
  }

def withScope (f : Scope → Scope) (x : CommandElabM α) : CommandElabM α := do
  match (← get).scopes with
  | [] => x
  | h :: t =>
    try
      modify fun s => { s with scopes := f h :: t }
      x
    finally
      modify fun s => { s with scopes := h :: t }

def getLevelNames : CommandElabM (List Name) :=
  return (← getScope).levelNames

def addUnivLevel (idStx : Syntax) : CommandElabM Unit := withRef idStx do
  let id := idStx.getId
  let levelNames ← getLevelNames
  if levelNames.elem id then
    throwAlreadyDeclaredUniverseLevel id
  else
    modifyScope fun scope => { scope with levelNames := id :: scope.levelNames }

end Elab.Command

open Elab Command MonadRecDepth

private def liftCommandElabMCore (cmd : CommandElabM α) (throwOnError : Bool) : CoreM α := do
  let s : Core.State ← get
  let ctx : Core.Context ← read
  let (a, commandState) ←
    cmd.run {
      fileName := ctx.fileName
      fileMap := ctx.fileMap
      currRecDepth := ctx.currRecDepth
      currMacroScope := ctx.currMacroScope
      ref := ctx.ref
      snap? := none
      cancelTk? := ctx.cancelTk?
      suppressElabErrors := ctx.suppressElabErrors
    } |>.run {
      env := s.env
      nextMacroScope := s.nextMacroScope
      maxRecDepth := ctx.maxRecDepth
      ngen := s.ngen
      scopes := [{ header := "", opts := ctx.options }]
      infoState.enabled := s.infoState.enabled
    }
  modify fun coreState => { coreState with
    env := commandState.env
    nextMacroScope := commandState.nextMacroScope
    ngen := commandState.ngen
    traceState.traces := coreState.traceState.traces ++ commandState.traceState.traces
  }
  if throwOnError then
    if let some err := commandState.messages.toArray.find? (·.severity matches .error) then
      throwError err.data
  modify fun coreState => { coreState with
    infoState.trees := coreState.infoState.trees.append commandState.infoState.trees
    messages := coreState.messages ++ commandState.messages
  }
  return a

/--
Lifts an action in `CommandElabM` into `CoreM`, updating the environment,
messages, info trees, traces, the name generator, and macro scopes.
The action is run in a context with an empty message log, empty trace state, and empty info trees.

If `throwOnError` is true, then if the command produces an error message, it is converted into an exception.
In this case, info trees and messages are not carried over.

Commands that modify the processing of subsequent commands,
such as `open` and `namespace` commands,
only have an effect for the remainder of the `CommandElabM` computation passed here,
and do not affect subsequent commands.

*Warning:* when using this from `MetaM` monads, the caches are *not* reset.
If the command defines new instances for example, you should use `Lean.Meta.resetSynthInstanceCache`
to reset the instance cache.
While the `modifyEnv` function for `MetaM` clears its caches entirely,
`liftCommandElabM` has no way to reset these caches.
-/
def liftCommandElabM (cmd : CommandElabM α) (throwOnError : Bool := true) : CoreM α := do
  -- `observing` ensures that if `cmd` throws an exception we still thread state back to `CoreM`.
  MonadExcept.ofExcept (← liftCommandElabMCore (observing cmd) throwOnError)

/--
Given a command elaborator `cmd`, returns a new command elaborator that
first evaluates any local `set_option ... in ...` clauses and then invokes `cmd` on what remains.
-/
partial def withSetOptionIn (cmd : CommandElab) : CommandElab := fun stx => do
  if stx.getKind == ``Lean.Parser.Command.in &&
     stx[0].getKind == ``Lean.Parser.Command.set_option then
      let opts ← Elab.elabSetOption stx[0][1] stx[0][3]
      Command.withScope (fun scope => { scope with opts }) do
        withSetOptionIn cmd stx[2]
  else
    cmd stx

export Elab.Command (Linter addLinter)

end Lean
