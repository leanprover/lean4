/-
Copyright (c) 2023 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Implementation of the Lean language: parsing and processing of header and commands, incremental
recompilation

Authors: Sebastian Ullrich
-/

prelude
import Lean.Language.Basic
import Lean.Language.Lean.Types
import Lean.Parser.Module
import Lean.Elab.Import

/-!
# Note [Incremental Parsing]

In the language server, we want to minimize the work we do after each edit by reusing previous state
where possible. This is true for both parsing, i.e. reusing syntax trees without running the parser,
and elaboration. For both, we currently assume that we have to reprocess at least everything from
the point of change downwards. This note is about how to find the correct starting point for
incremental parsing; for elaboration, we then start with the first changed syntax tree.

One initial thought about incremental parsing could be that it's not necessary as parsing is very
fast compared to elaboration; on mathlib we average 41ms parsing per 1000 LoC. But there are quite a
few files >= 1kloc (up to 4.5kloc) in there, so near the end of such files lag from always reparsing
from the beginning may very well be noticeable.

So if we do want incremental parsing, another thought might be that a user edit can only invalidate
commands at or after the location of the change. Unfortunately, that's not true; take the (partial)
input `def a := b private def c`. If we remove the space after `private`, the two commands
syntactically become one with an application of `privatedef` to `b` even though the edit was
strictly after the end of the first command.

So obviously we must include at least the extent of the token that made the parser stop parsing a
command as well such that invalidating the private token invalidates the preceding command.
Unfortunately this is not sufficient either, given the following input:
```
structure a where /-- b -/ @[c] private axiom d : Nat
```
This is a syntactically valid sequence of a field-less structure and a declaration. If we again
delete the space after private, it becomes a syntactically correct structure with a single field
privateaxiom! So clearly, because of uses of atomic in the grammar, an edit can affect a command
syntax tree even across multiple tokens.

Now, what we do today, and have done since Lean 3, is to always reparse the last command completely
preceding the edit location. If its syntax tree is unchanged, we preserve its data and reprocess all
following commands only, otherwise we reprocess it fully as well. This seems to have worked well so
far but it does seem a bit arbitrary given that even if it works for our current grammar, it can
certainly be extended in ways that break the assumption.

Finally, a more actually principled and generic solution would be to invalidate a syntax tree when
the parser has reached the edit location during parsing. If it did not, surely the edit cannot have
an effect on the syntax tree in question. Sadly such a "high-water mark" parser position does not
exist currently and likely it could at best be approximated by e.g. "furthest `tokenFn` parse". Thus
we remain at "go two commands up" at this point.
-/

/-!
# Note [Incremental Command Elaboration]

Because of Lean's use of persistent data structures, incremental reuse of fully elaborated commands
is easy because we can simply snapshot the entire state after each command and then restart
elaboration using the stored state at the next command above the point of change. However,
incrementality *within* elaboration of a single command such as between tactic steps is much harder
because the existing control flow does not allow us to simply return from those points to the
language processor in a way that we can later resume from there. Instead, we exchange the need for
continuations with some limited mutability: by allocating an `IO.Promise` "cell" in the language
processor, we can both pass it to the elaborator to eventually fill it using `Promise.resolve` as
well as convert it to a `Task` that will wait on that resolution using `Promise.result` and return
it as part of the command snapshot created by the language processor. The elaborator can then in
turn create new promises itself and store their `result` when resolving an outer promise to create
an arbitrary tree of promise-backed snapshot tasks. Thus, we can enable incremental reporting and
reuse inside the elaborator using the same snapshot tree data structures as outside without having
to change the elaborator's control flow.

While ideally we would decide what can be reused during command elaboration using strong hashes over
the full state and inputs, currently we rely on simpler syntactic checks: if all the syntax
inspected up to a certain point is unchanged, we can assume that the old state can be reused. The
central `SnapshotBundle` type passed inwards through the elaborator for this purpose combines the
following data:
* the `IO.Promise` to be resolved to an elaborator snapshot (whose type depends on the specific
  elaborator part we're in, e.g. `TacticParsedSnapshot`, `BodyProcessedSnapshot`)
* if there was a previous run:
  * a `SnapshotTask` holding the corresponding snapshot of the run
  * the relevant `Syntax` of the previous run to be compared before any reuse

Note that as we do not wait for the previous run to finish before starting to elaborate the next
one, the old `SnapshotTask` task may not be finished yet. Indeed, if we do find that we can reuse
the contained state because of a successful syntax comparison, we always want to explicitly wait for
the task instead of redoing the work. On the other hand, the `Syntax` is not surrounded by a task so
that we can immediately access it for comparisons, even if the snapshot task may, eventually, give
access to the same syntax tree.

For the most part, inside an elaborator participating in incrementality, we just have to ensure that
we stop forwarding the old run's data as soon as we notice a relevant difference between old and new
syntax tree. For example, allowing incrementality inside the cdot tactic combinator is as simple as
```
builtin_initialize registerBuiltinIncrementalTactic ``cdot
@[builtin_tactic cdot] def evalTacticCDot : Tactic := fun stx => do
  ...
  closeUsingOrAdmit do
    -- save state before/after entering focus on `·`
    ...
    Term.withNarrowedArgTacticReuse (argIdx := 1) evalTactic stx
```
The `Term.withNarrowedArgTacticReuse` combinator will focus on the given argument of `stx`, which in
this case is the nested tactic sequence, and run `evalTactic` on it. But crucially, it will first
compare all preceding arguments, in this case the cdot token itself, with the old syntax in the
current snapshot bundle, which in the case of tactics is stored in `Term.Context.tacSnap?`. Indeed
it is important here to check if the cdot token is identical because its position has been saved in
the info tree, so it would be bad if we later restored some old state that uses a different position
for it even if everything else is unchanged.  If there is any mismatch, the bundle's old value is
set to `none` in order to prevent reuse from this point on. Note that in any case we still want to
forward the "new" promise in order to provide incremental reporting as well as to construct a
snapshot tree for reuse in future document versions! Note also that we explicitly opted into
incrementality using `registerBuiltinIncrementalTactic` as any tactic combinator not written with
these concerns in mind would likely misbehave under incremental reuse.

While it is generally true that we can provide incremental reporting even without reuse, we
generally want to avoid that when it would be confusing/annoying, e.g. when a tactic block is run
multiple times because otherwise the progress bar would snap back and forth multiple times. For this
purpose, we can disable both incremental modes using `Term.withoutTacticIncrementality`, assuming we
opted into incrementality because of other parts of the combinator. `induction` is an example of
this because there are some induction alternatives that are run multiple times, so we disable all of
incrementality for them.

Using `induction` as a more complex example than `cdot` as it calls into `evalTactic` multiple
times, here is a summary of what it has to do to implement incrementality:
* `Narrow` down to the syntax of alternatives, disabling reuse if anything before them changed
* allocate one new promise for each given alternative, immediately resolve passed promise to a new
  snapshot tree node holding them so that the language server can wait on them
* when executing an alternative,
  * we put the corresponding promise into the context
  * we disable reuse if anything in front of the contained tactic block has changed, including
    previous alternatives
  * we disable reuse *and reporting* if the tactic block is run multiple times, e.g. in the case of
    a wildcard pattern
-/

/-
# Note [Incremental Macros]

If we have a macro, we can cheaply support incrementality: as a macro is a pure function, if all
outputs apart from the expanded syntax tree itself are identical in two document versions, we can
simply delegate reuse detection to the subsequently called elaborator. All we have to do is to
forward the old unfolding, if any, to it in the appropriate context field and store the new
unfolding for that purpose in a new snapshot node whose child will be filled by the called
elaborator. This is currently implemented for command and tactic macros.

Caveat 1: Traces are an additional output of macro expansion but because they are hard to compare
and should not be active in standard use cases, we disable incrementality if either version produced
traces.

Caveat 2: As the default `ref` of a macro spans its entire syntax tree and is applied to any token
created from a quotation, the ref usually has to be changed to a less variable source using
`withRef` to achieve effective incrementality. See `Elab.Command.expandNamespacedDeclaration` for a
simple example and the implementation of tactic `have` for a complex example.
-/

set_option linter.missingDocs true

namespace Lean.Language.Lean
open Lean.Elab Command
open Lean.Parser

/-- Option for capturing output to stderr during elaboration. -/
register_builtin_option stderrAsMessages : Bool := {
  defValue := true
  group    := "server"
  descr    := "(server) capture output to the Lean stderr channel (such as from `dbg_trace`) during elaboration of a command as a diagnostic message"
}

/-- Lean-specific processing context. -/
structure LeanProcessingContext extends ProcessingContext where
  /-- Position of the first file difference if there was a previous invocation. -/
  firstDiffPos? : Option String.Pos
  /-- Cancellation token of the previous invocation, if any. -/
  oldCancelTk? : Option IO.CancelToken
  /-- Cancellation token of the current run. -/
  newCancelTk : IO.CancelToken

/-- Monad transformer holding all relevant data for Lean processing. -/
abbrev LeanProcessingT m := ReaderT LeanProcessingContext m
/-- Monad holding all relevant data for Lean processing. -/
abbrev LeanProcessingM := LeanProcessingT BaseIO

instance : MonadLift LeanProcessingM (LeanProcessingT IO) where
  monadLift := fun act ctx => act ctx

instance : MonadLift (ProcessingT m) (LeanProcessingT m) where
  monadLift := fun act ctx => act ctx.toProcessingContext

/--
Embeds a `LeanProcessingM` action into `ProcessingM`, optionally using the old input string to speed
up reuse analysis and supplying a cancellation token that should be triggered as soon as reuse is
ruled out.
-/
def LeanProcessingM.run (act : LeanProcessingM α) (oldInputCtx? : Option InputContext)
    (oldCancelTk? : Option IO.CancelToken := none) : ProcessingM α := do
  -- compute position of syntactic change once
  let firstDiffPos? := oldInputCtx?.map (·.input.firstDiffPos (← read).input)
  let newCancelTk ← IO.CancelToken.new
  ReaderT.adapt ({ · with firstDiffPos?, oldCancelTk?, newCancelTk }) act

/--
Returns true if there was a previous run and the given position is before any textual change
compared to it.
-/
def isBeforeEditPos (pos : String.Pos) : LeanProcessingM Bool := do
  return (← read).firstDiffPos?.any (pos < ·)

/--
  Adds unexpected exceptions from header processing to the message log as a last resort; standard
  errors should already have been caught earlier. -/
private def withHeaderExceptions (ex : Snapshot → α) (act : LeanProcessingT IO α) :
    LeanProcessingM α := do
  match (← (act (← read)).toBaseIO) with
  | .error e => return ex { diagnostics := (← diagnosticsOfHeaderError e.toString) }
  | .ok a => return a

/--
Result of retrieving additional metadata about the current file after parsing imports. In the
language server, these are derived from the `lake setup-file` result. On the cmdline and for similar
simple uses, these can be computed eagerly without looking at the imports.
-/
structure SetupImportsResult where
  /-- Module name of the file being processed. -/
  mainModuleName : Name
  /-- Options provided outside of the file content, e.g. on the cmdline or in the lakefile. -/
  opts : Options
  /-- Kernel trust level. -/
  trustLevel : UInt32 := 0

/-- Performance option used by cmdline driver. -/
register_builtin_option internal.cmdlineSnapshots : Bool := {
  defValue := false
  descr    := "mark persistent and reduce information stored in snapshots to the minimum necessary \
    for the cmdline driver: diagnostics per command and final full snapshot"
}

/--
Parses values of options registered during import and left by the C++ frontend as strings, fails if
any option names remain unknown.
-/
def reparseOptions (opts : Options) : IO Options := do
  let mut opts := opts
  let decls ← getOptionDecls
  for (name, val) in opts do
    let .ofString val := val
      | continue  -- Already parsed by C++
    -- Options can be prefixed with `weak` in order to turn off the error when the option is not
    -- defined
    let weak := name.getRoot == `weak
    if weak then
      opts := opts.erase name
    let name := name.replacePrefix `weak Name.anonymous
    let some decl := decls.find? name
      | unless weak do
          throw <| .userError s!"invalid -D parameter, unknown configuration option '{name}'

If the option is defined in this library, use '-D{`weak ++ name}' to set it conditionally"

    match decl.defValue with
    | .ofBool _ =>
      match val with
      | "true"  => opts := opts.insert name true
      | "false" => opts := opts.insert name false
      | _ =>
        throw <| .userError s!"invalid -D parameter, invalid configuration option '{val}' value, \
          it must be true/false"
    | .ofNat _ =>
      let some val := val.toNat?
        | throw <| .userError s!"invalid -D parameter, invalid configuration option '{val}' value, \
            it must be a natural number"
      opts := opts.insert name val
    | .ofString _ => opts := opts.insert name val
    | _ => throw <| .userError s!"invalid -D parameter, configuration option '{name}' \
              cannot be set in the command line, use set_option command"

  return opts

/--
Entry point of the Lean language processor.

The `setupImports` function is called after the header has been parsed and before the first command
is parsed in order to supply additional file metadata (or abort with a given terminal snapshot); see
`SetupImportsResult`.

`old?` is a previous resulting snapshot, if any, to be reused for incremental processing.
-/
/-
General notes:
* For each processing function we pass in the previous state, if any, in order to reuse still-valid
  state. As there is no cheap way to check whether the `Environment` is unchanged, i.e. *semantic*
  change detection is currently not possible, we must make sure to pass `none` as all follow-up
  "previous states" from the first *syntactic* change onwards.
* We must make sure to trigger `oldCancelTk?` as soon as discarding `old?`.
* Control flow up to finding the last still-valid snapshot (which should be quick) is synchronous so
  as not to report this "fast forwarding" to the user as well as to make sure the next run sees all
  fast-forwarded snapshots without having to wait on tasks. It also ensures this part cannot be
  delayed by threadpool starvation. We track whether we are still on the fast-forwarding path using
  the `sync` parameter on `parseCmd` and spawn an elaboration task when we leave it.
-/
partial def process
    (setupImports : Syntax → ProcessingT IO (Except HeaderProcessedSnapshot SetupImportsResult))
    (old? : Option InitialSnapshot) : ProcessingM InitialSnapshot := do
  parseHeader old? |>.run (old?.map (·.ictx)) (old?.bind (·.cancelTk?))
where
  parseHeader (old? : Option HeaderParsedSnapshot) : LeanProcessingM HeaderParsedSnapshot := do
    let ctx ← read
    let ictx := ctx.toInputContext
    let unchanged old newStx newParserState :=
      -- when header syntax is unchanged, reuse import processing task as is and continue with
      -- parsing the first command, synchronously if possible
      -- NOTE: even if the syntax tree is functionally unchanged, its concrete structure and the new
      -- parser state may still have changed because of trailing whitespace and comments etc., so
      -- they are passed separately from `old`
      if let some oldSuccess := old.result? then
        return {
          ictx
          stx := newStx
          diagnostics := old.diagnostics
          cancelTk? := ctx.newCancelTk
          result? := some {
            parserState := newParserState
            processedSnap := (← oldSuccess.processedSnap.bindIO (sync := true) fun oldProcessed => do
              if let some oldProcSuccess := oldProcessed.result? then
                -- also wait on old command parse snapshot as parsing is cheap and may allow for
                -- elaboration reuse
                oldProcSuccess.firstCmdSnap.bindIO (sync := true) fun oldCmd => do
                  let prom ← IO.Promise.new
                  parseCmd oldCmd newParserState oldProcSuccess.cmdState prom (sync := true) ctx
                  return .pure {
                    diagnostics := oldProcessed.diagnostics
                    result? := some {
                      cmdState := oldProcSuccess.cmdState
                      firstCmdSnap := { range? := none, task := prom.result } } }
              else
                return .pure oldProcessed) } }
      else return old

    -- fast path: if we have parsed the header successfully...
    if let some old := old? then
      if let some oldSuccess := old.result? then
        if let some (some processed) ← old.processedResult.get? then
          -- ...and the edit location is after the next command (see note [Incremental Parsing])...
          if let some nextCom ← processed.firstCmdSnap.get? then
            if (← isBeforeEditPos nextCom.data.parserState.pos) then
              -- ...go immediately to next snapshot
              return (← unchanged old old.stx oldSuccess.parserState)

    withHeaderExceptions ({ · with
        ictx, stx := .missing, result? := none, cancelTk? := none }) do
      -- parsing the header should be cheap enough to do synchronously
      let (stx, parserState, msgLog) ← Parser.parseHeader ictx
      if msgLog.hasErrors then
        return {
          ictx, stx
          diagnostics := (← Snapshot.Diagnostics.ofMessageLog msgLog)
          result? := none
          cancelTk? := none
        }

      let trimmedStx := stx.unsetTrailing
      -- semi-fast path: go to next snapshot if syntax tree is unchanged
      -- NOTE: We compare modulo `unsetTrailing` in order to ensure that changes in trailing
      -- whitespace do not invalidate the header. This is safe because we only pass the trimmed
      -- syntax tree to `processHeader` below, so there cannot be any references to the trailing
      -- whitespace in its result. We still store the untrimmed syntax tree in the snapshot in order
      -- to uphold the invariant that concatenating all top-level snapshots' syntax trees results in
      -- the original file.
      if let some old := old? then
        if trimmedStx.eqWithInfo old.stx.unsetTrailing then
          -- Here we must make sure to pass the *new* syntax and parser state; see NOTE in
          -- `unchanged`
          return (← unchanged old stx parserState)
        -- on first change, make sure to cancel old invocation
        if let some tk := ctx.oldCancelTk? then
          tk.set
      return {
        ictx, stx
        diagnostics := (← Snapshot.Diagnostics.ofMessageLog msgLog)
        result? := some {
          parserState
          processedSnap := (← processHeader trimmedStx parserState)
        }
        cancelTk? := ctx.newCancelTk
      }

  processHeader (stx : Syntax) (parserState : Parser.ModuleParserState) :
      LeanProcessingM (SnapshotTask HeaderProcessedSnapshot) := do
    let ctx ← read
    SnapshotTask.ofIO (some ⟨0, ctx.input.endPos⟩) <|
    ReaderT.run (r := ctx) <|  -- re-enter reader in new task
    withHeaderExceptions (α := HeaderProcessedSnapshot) ({ · with result? := none }) do
      let setup ← match (← setupImports stx) with
        | .ok setup => pure setup
        | .error snap => return snap

      let startTime := (← IO.monoNanosNow).toFloat / 1000000000
      -- allows `headerEnv` to be leaked, which would live until the end of the process anyway
      let (headerEnv, msgLog) ← Elab.processHeader (leakEnv := true) stx setup.opts .empty
        ctx.toInputContext setup.trustLevel
      let stopTime := (← IO.monoNanosNow).toFloat / 1000000000
      let diagnostics := (← Snapshot.Diagnostics.ofMessageLog msgLog)
      if msgLog.hasErrors then
        return { diagnostics, result? := none }

      let headerEnv := headerEnv.setMainModule setup.mainModuleName
      let mut traceState := default
      if trace.profiler.output.get? setup.opts |>.isSome then
        traceState := {
          traces := #[{
            ref := .missing,
            msg := .trace { cls := `Import, startTime, stopTime }
              (.ofFormat "importing") #[]
            : TraceElem
          }].toPArray'
        }
      -- now that imports have been loaded, check options again
      let opts ← reparseOptions setup.opts
      let cmdState := Elab.Command.mkState headerEnv msgLog opts
      let cmdState := { cmdState with
        infoState := {
          enabled := true
          trees := #[Elab.InfoTree.context (.commandCtx {
            env     := headerEnv
            fileMap := ctx.fileMap
            ngen    := { namePrefix := `_import }
          }) (Elab.InfoTree.node
              (Elab.Info.ofCommandInfo { elaborator := `header, stx })
              (stx[1].getArgs.toList.map (fun importStx =>
                Elab.InfoTree.node (Elab.Info.ofCommandInfo {
                  elaborator := `import
                  stx := importStx
                }) #[].toPArray'
              )).toPArray'
          )].toPArray'
        }
        traceState
      }
      let prom ← IO.Promise.new
      -- The speedup of these `markPersistent`s is negligible but they help in making unexpected
      -- `inc_ref_cold`s more visible
      let parserState := Runtime.markPersistent parserState
      let cmdState := Runtime.markPersistent cmdState
      let ctx := Runtime.markPersistent ctx
      parseCmd none parserState cmdState prom (sync := true) ctx
      return {
        diagnostics
        infoTree? := cmdState.infoState.trees[0]!
        result? := some {
          cmdState
          firstCmdSnap := { range? := none, task := prom.result }
        }
      }

  parseCmd (old? : Option CommandParsedSnapshot) (parserState : Parser.ModuleParserState)
      (cmdState : Command.State) (prom : IO.Promise CommandParsedSnapshot) (sync : Bool) :
      LeanProcessingM Unit := do
    let ctx ← read

    let unchanged old newParserState : BaseIO Unit :=
      -- when syntax is unchanged, reuse command processing task as is
      -- NOTE: even if the syntax tree is functionally unchanged, the new parser state may still
      -- have changed because of trailing whitespace and comments etc., so it is passed separately
      -- from `old`
      if let some oldNext := old.nextCmdSnap? then do
        let newProm ← IO.Promise.new
        let _ ← old.data.finishedSnap.bindIO (sync := true) fun oldFinished =>
          -- also wait on old command parse snapshot as parsing is cheap and may allow for
          -- elaboration reuse
          oldNext.bindIO (sync := true) fun oldNext => do
            parseCmd oldNext newParserState oldFinished.cmdState newProm sync ctx
            return .pure ()
        prom.resolve <| .mk (data := old.data) (nextCmdSnap? := some { range? := none, task := newProm.result })
      else prom.resolve old  -- terminal command, we're done!

    -- fast path, do not even start new task for this snapshot
    if let some old := old? then
      if let some nextCom ← old.nextCmdSnap?.bindM (·.get?) then
        if (← isBeforeEditPos nextCom.data.parserState.pos) then
          return (← unchanged old old.data.parserState)

    let beginPos := parserState.pos
    let scope := cmdState.scopes.head!
    let pmctx := {
      env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace
      openDecls := scope.openDecls
    }
    let (stx, parserState, msgLog) :=
      profileit "parsing" scope.opts fun _ =>
        Parser.parseCommand ctx.toInputContext pmctx parserState .empty

    -- semi-fast path
    if let some old := old? then
      -- NOTE: as `parserState.pos` includes trailing whitespace, this forces reprocessing even if
      -- only that whitespace changes, which is wasteful but still necessary because it may
      -- influence the range of error messages such as from a trailing `exact`
      if stx.eqWithInfo old.data.stx then
        -- Here we must make sure to pass the *new* parser state; see NOTE in `unchanged`
        return (← unchanged old parserState)
      -- on first change, make sure to cancel old invocation
      -- TODO: pass token into incrementality-aware elaborators to improve reuse of still-valid,
      -- still-running elaboration steps?
      if let some tk := ctx.oldCancelTk? then
        tk.set

    -- check for cancellation, most likely during elaboration of previous command, before starting
    -- processing of next command
    if (← ctx.newCancelTk.isSet) then
      -- this is a bit ugly as we don't want to adjust our API with `Option`s just for cancellation
      -- (as no-one should look at this result in that case) but anything containing `Environment`
      -- is not `Inhabited`
      prom.resolve <| .mk (nextCmdSnap? := none) {
        diagnostics := .empty, stx := .missing, parserState
        elabSnap := .pure <| .ofTyped { diagnostics := .empty : SnapshotLeaf }
        finishedSnap := .pure { diagnostics := .empty, cmdState }
        tacticCache := (← IO.mkRef {})
      }
      return

    -- Start new task when leaving fast-forwarding path; see "General notes" above
    let _ ← (if sync then BaseIO.asTask else (.pure <$> ·)) do
      -- definitely resolved in `doElab` task
      let elabPromise ← IO.Promise.new
      let finishedPromise ← IO.Promise.new
      -- (Try to) use last line of command as range for final snapshot task. This ensures we do not
      -- retract the progress bar to a previous position in case the command support incremental
      -- reporting but has significant work after resolving its last incremental promise, such as
      -- final type checking; if it does not support incrementality, `elabSnap` constructed in
      -- `parseCmd` and containing the entire range of the command will determine the reported
      -- progress and be resolved effectively at the same time as this snapshot task, so `tailPos` is
      -- irrelevant in this case.
      let endRange? := stx.getTailPos?.map fun pos => ⟨pos, pos⟩
      let finishedSnap := { range? := endRange?, task := finishedPromise.result }
      let tacticCache ← old?.map (·.data.tacticCache) |>.getDM (IO.mkRef {})

      let minimalSnapshots := internal.cmdlineSnapshots.get cmdState.scopes.head!.opts
      let next? ← if Parser.isTerminalCommand stx then pure none
        -- for now, wait on "command finished" snapshot before parsing next command
        else some <$> IO.Promise.new
      let diagnostics ← Snapshot.Diagnostics.ofMessageLog msgLog
      let data := if minimalSnapshots && !Parser.isTerminalCommand stx then {
        diagnostics
        stx := .missing
        parserState := {}
        elabSnap := { range? := stx.getRange?, task := elabPromise.result }
        finishedSnap
        tacticCache
      } else {
        diagnostics, stx, parserState, tacticCache
        elabSnap := { range? := stx.getRange?, task := elabPromise.result }
        finishedSnap
      }
      prom.resolve <| .mk (nextCmdSnap? := next?.map
        ({ range? := some ⟨parserState.pos, ctx.input.endPos⟩, task := ·.result })) data
      let cmdState ← doElab stx cmdState beginPos
        { old? := old?.map fun old => ⟨old.data.stx, old.data.elabSnap⟩, new := elabPromise }
        finishedPromise tacticCache ctx
      if let some next := next? then
        -- We're definitely off the fast-forwarding path now
        parseCmd none parserState cmdState next (sync := false) ctx

  doElab (stx : Syntax) (cmdState : Command.State) (beginPos : String.Pos)
      (snap : SnapshotBundle DynamicSnapshot) (finishedPromise : IO.Promise CommandFinishedSnapshot)
      (tacticCache : IO.Ref Tactic.Cache) :
      LeanProcessingM Command.State := do
    let ctx ← read
    let scope := cmdState.scopes.head!
    let cmdStateRef ← IO.mkRef { cmdState with messages := .empty }
    /-
    The same snapshot may be executed by different tasks. So, to make sure `elabCommandTopLevel`
    has exclusive access to the cache, we create a fresh reference here. Before this change, the
    following `tacticCache.modify` would reset the tactic post cache while another snapshot was
    still using it.
    -/
    let tacticCacheNew ← IO.mkRef (← tacticCache.get)
    let cmdCtx : Elab.Command.Context := { ctx with
      cmdPos       := beginPos
      tacticCache? := some tacticCacheNew
      snap?        := if internal.cmdlineSnapshots.get scope.opts then none else snap
      cancelTk?    := some ctx.newCancelTk
    }
    let (output, _) ←
      IO.FS.withIsolatedStreams (isolateStderr := stderrAsMessages.get scope.opts) do
        liftM (m := BaseIO) do
          withLoggingExceptions
            (getResetInfoTrees *> Elab.Command.elabCommandTopLevel stx)
            cmdCtx cmdStateRef
    let postNew := (← tacticCacheNew.get).post
    tacticCache.modify fun _ => { pre := postNew, post := {} }
    let cmdState ← cmdStateRef.get
    let mut messages := cmdState.messages
    if !output.isEmpty then
      messages := messages.add {
        fileName := ctx.fileName
        severity := MessageSeverity.information
        pos      := ctx.fileMap.toPosition beginPos
        data     := output
      }
    let cmdState := { cmdState with messages }
    -- definitely resolve eventually
    snap.new.resolve <| .ofTyped { diagnostics := .empty : SnapshotLeaf }

    let mut infoTree := cmdState.infoState.trees[0]!
    let cmdline := internal.cmdlineSnapshots.get scope.opts && !Parser.isTerminalCommand stx
    if cmdline then
      infoTree := Runtime.markPersistent infoTree
    finishedPromise.resolve {
      diagnostics := (← Snapshot.Diagnostics.ofMessageLog cmdState.messages)
      infoTree? := infoTree
      cmdState := if cmdline then {
        env := Runtime.markPersistent cmdState.env
        maxRecDepth := 0
      } else cmdState
    }
    -- The reported `cmdState` in the snapshot may be minimized as seen above, so we return the full
    -- state here for further processing on the same thread
    return cmdState

/--
Convenience function for tool uses of the language processor that skips header handling.
-/
def processCommands (inputCtx : Parser.InputContext) (parserState : Parser.ModuleParserState)
    (commandState : Command.State)
    (old? : Option (Parser.InputContext × CommandParsedSnapshot) := none) :
    BaseIO (Task CommandParsedSnapshot) := do
  let prom ← IO.Promise.new
  process.parseCmd (old?.map (·.2)) parserState commandState prom (sync := true)
    |>.run (old?.map (·.1))
    |>.run { inputCtx with }
  return prom.result

/-- Waits for and returns final command state, if importing was successful. -/
partial def waitForFinalCmdState? (snap : InitialSnapshot) : Option Command.State := do
  let snap ← snap.result?
  let snap ← snap.processedSnap.get.result?
  goCmd snap.firstCmdSnap.get
where goCmd snap :=
  if let some next := snap.nextCmdSnap? then
    goCmd next.get
  else
    snap.data.finishedSnap.get.cmdState

end Lean
