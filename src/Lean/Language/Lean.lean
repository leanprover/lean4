/-
Copyright (c) 2023 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Implementation of the Lean language: parsing and processing of header and commands, incremental
recompilation

Authors: Sebastian Ullrich
-/

prelude
import Lean.Language.Basic
import Lean.Language.Util
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

What we did in Lean 3 was to always reparse the last command completely preceding the edit location.
If its syntax tree is unchanged, we preserve its data and reprocess all following commands only,
otherwise we reprocess it fully as well. This worked well but did seem a bit arbitrary given that
even if it works for a grammar at some point, it can certainly be extended in ways that break the
assumption.

With grammar changes in Lean 4, we found that the following example indeed breaks this assumption:
```
structure Signature where
  /-- a docstring -/
  Sort : Type
    --^ insert: "s"
```
As the keyword `Sort` is not a valid start of a structure field and the parser backtracks across the
docstring in that case, this is parsed as the complete command `structure Signature where` followed
by the partial command `/-- a docstring -/ <missing>`. If we insert an `s` after the `t`, the last
command completely preceding the edit location is the partial command containing the docstring. Thus
we need to go up two commands to ensure we reparse the `structure` command as well. This kind of
nested docstring is the only part of the grammar to our knowledge that requires going up at least
two commands; as we never backtrack across more than one docstring, going up two commands should
also be sufficient.

Finally, a more actually principled and generic solution would be to invalidate a syntax tree when
the parser has reached the edit location during parsing. If it did not, surely the edit cannot have
an effect on the syntax tree in question. Sadly such a "high-water mark" parser position does not
exist currently and likely it could at best be approximated by e.g. "furthest `tokenFn` parse". Thus
we remain at "go up two commands" at this point.
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

/-
# Note [Incremental Cancellation]

With incrementality, there is a tension between telling the elaboration of the previous document
version(s) to stop processing as soon as possible in order to free resources for use in the current
elaboration run and having the old version continue in case its results can be used as is so as not
to duplicate effort.

Before parallelism, we were able to use a single cancellation token for the entire elaboration of a
specific document version. We could trigger the cancellation token as soon as we started elaborating
a new version because the generated exceptions would prevent the elaborator from storing any
half-elaborated state in snapshots that might then be picked up for reuse. This was a simple and
sound solution, though it did mean we may have cancelled some work eagerly that could have been
reused.

This approach is no longer sound with parallelism: a tactic may have spawned async tasks (e.g.
kernel checking of a helper definition) and then completed, creating a snapshot that references the
result of the task e.g. via an asynchronous constant in the environment. If we then interrupted
elaboration of that document version throughout all its tasks, we might end up with a snapshot that
looks eligible for reuse but references data (eventually) resulting from cancellation. We could
(asynchronously) wait for it to complete and then check whether it completed because of cancellation
and redo its work in that case but that would be as wasteful as mentioned above and add new latency
on top.

Instead, we now make sure we cancel only the parts of elaboration we have ruled out for reuse, at
the earliest point where we can decide that. We do this by storing cancellation tokens in the
snapshot tree such that we can trigger all tokens of tasks belonging to a specific subtree
(`SnapshotTask.cancelRec`; async tasks belonging to the subtree are usually collected via
`Core.getAndEmptySnapshotTasks`). Thus when traversing the old snapshot tree, we need to be careful
about cancelling any children we decide not to descend into. This is automated in e.g.
`withNarrowedTacticReuse` but not in other places that do not lend themselves to abstraction into
combinators. Note that we can still cancel parsing and elaboration below the changed command eagerly
as we never consider them for reuse.

This approach is still not optimal in the sense that async tasks in later snapshots not part of the
current subtree are considered for cancellation only when elaboration reaches that point. Thus if
inside a single proof we have some significant work done synchronously by one tactic and then
significant work done asynchronously by a later tactic and neither tactic is eligible for reuse, the
second task will only be cancelled after redoing the synchronous work up to the point of the second
tactic. However, as tactics such as `bv_decide` that do significant kernel work do so synchronously
at the moment in order to post-process any failures and as the most significant async work, that of
checking/compiling/linting/... the top-level definition, is interrupted immediately when the mutual
def elaborator notices that the body syntax has changed, this should not be a significant issue in
practice. If we do want to optimize this, instead of cancelling subtrees of the snapshot tree, we
would likely have to store an asynchronously resolved list of cancellation tokens associated with
the tactic snapshot at hand *and all further snapshots* so that we can cancel them eagerly instead
of waiting for elaboration to visit those later snapshots.
-/

set_option linter.missingDocs true

namespace Lean.Language.Lean
open Lean.Elab Command
open Lean.Parser

/-- Lean-specific processing context. -/
structure LeanProcessingContext extends ProcessingContext where
  /-- Position of the first file difference if there was a previous invocation. -/
  firstDiffPos? : Option String.Pos

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
def LeanProcessingM.run (act : LeanProcessingM α) (oldInputCtx? : Option InputContext) :
    ProcessingM α := do
  -- compute position of syntactic change once
  let firstDiffPos? := oldInputCtx?.map (·.input.firstDiffPos (← read).input)
  ReaderT.adapt ({ · with firstDiffPos? }) act

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
  /-- Lean plugins to load as part of the environment setup. -/
  plugins : Array System.FilePath := #[]

/-- Performance option used by cmdline driver. -/
register_builtin_option internal.cmdlineSnapshots : Bool := {
  defValue := false
  descr    := "reduce information stored in snapshots to the minimum necessary \
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

private def getNiceCommandStartPos? (stx : Syntax) : Option String.Pos := do
  let mut stx := stx
  if stx[0].isOfKind ``Command.declModifiers then
    -- modifiers are morally before the actual declaration
    stx := stx[1]
  stx.getPos?

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
  parseHeader old? |>.run (old?.map (·.ictx))
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
        -- make sure to update ranges of all reused tasks
        let progressRange? := some ⟨newParserState.pos, ctx.input.endPos⟩
        return {
          ictx
          stx := newStx
          diagnostics := old.diagnostics
          result? := some {
            parserState := newParserState
            processedSnap := (← oldSuccess.processedSnap.bindIO (stx? := newStx)
                (cancelTk? := none) (reportingRange? := progressRange?) (sync := true) fun oldProcessed => do
              if let some oldProcSuccess := oldProcessed.result? then
                -- also wait on old command parse snapshot as parsing is cheap and may allow for
                -- elaboration reuse
                oldProcSuccess.firstCmdSnap.bindIO (sync := true) (stx? := newStx)
                    (cancelTk? := none) (reportingRange? := progressRange?) fun oldCmd => do
                  let prom ← IO.Promise.new
                  let cancelTk ← IO.CancelToken.new
                  parseCmd oldCmd newParserState oldProcSuccess.cmdState prom (sync := true) cancelTk ctx
                  return .finished newStx {
                    diagnostics := oldProcessed.diagnostics
                    result? := some {
                      cmdState := oldProcSuccess.cmdState
                      firstCmdSnap := { stx? := none, task := prom.result! } } }
              else
                return .finished newStx oldProcessed) } }
      else return old

    -- fast path: if we have parsed the header successfully...
    if let some old := old? then
      if let some oldSuccess := old.result? then
        if let some (some processed) ← old.processedResult.get? then
          -- ...and the edit is after the second-next command (see note [Incremental Parsing])...
          if let some nextCom ← processed.firstCmdSnap.get? then
            if let some nextNextCom ← processed.firstCmdSnap.get? then
              if (← isBeforeEditPos nextNextCom.parserState.pos) then
                -- ...go immediately to next snapshot
                return (← unchanged old old.stx oldSuccess.parserState)

    withHeaderExceptions ({ · with ictx, stx := .missing, result? := none }) do
      -- parsing the header should be cheap enough to do synchronously
      let (stx, parserState, msgLog) ← Parser.parseHeader ictx
      if msgLog.hasErrors then
        return {
          ictx, stx
          diagnostics := (← Snapshot.Diagnostics.ofMessageLog msgLog)
          result? := none
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
        old.result?.forM (·.processedSnap.cancelRec)
      return {
        ictx, stx
        diagnostics := (← Snapshot.Diagnostics.ofMessageLog msgLog)
        result? := some {
          parserState
          processedSnap := (← processHeader trimmedStx parserState)
        }
      }

  processHeader (stx : Syntax) (parserState : Parser.ModuleParserState) :
      LeanProcessingM (SnapshotTask HeaderProcessedSnapshot) := do
    let ctx ← read
    SnapshotTask.ofIO stx (some ⟨0, ctx.input.endPos⟩) <|
    ReaderT.run (r := ctx) <|  -- re-enter reader in new task
    withHeaderExceptions (α := HeaderProcessedSnapshot) ({ · with result? := none }) do
      let setup ← match (← setupImports stx) with
        | .ok setup => pure setup
        | .error snap => return snap

      let startTime := (← IO.monoNanosNow).toFloat / 1000000000
      -- allows `headerEnv` to be leaked, which would live until the end of the process anyway
      let (headerEnv, msgLog) ← Elab.processHeader (leakEnv := true) stx setup.opts .empty
        ctx.toInputContext setup.trustLevel setup.plugins
      let stopTime := (← IO.monoNanosNow).toFloat / 1000000000
      let diagnostics := (← Snapshot.Diagnostics.ofMessageLog msgLog)
      if msgLog.hasErrors then
        return { diagnostics, result? := none }

      let headerEnv := headerEnv.setMainModule setup.mainModuleName
      let headerEnv ← headerEnv.enableRealizationsForImports setup.opts
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
      let cancelTk ← IO.CancelToken.new
      parseCmd none parserState cmdState prom (sync := true) cancelTk ctx
      return {
        diagnostics
        infoTree? := cmdState.infoState.trees[0]!
        result? := some {
          cmdState
          firstCmdSnap := { stx? := none, task := prom.result! }
        }
      }

  parseCmd (old? : Option CommandParsedSnapshot) (parserState : Parser.ModuleParserState)
      (cmdState : Command.State) (prom : IO.Promise CommandParsedSnapshot) (sync : Bool)
      (parseCancelTk : IO.CancelToken) : LeanProcessingM Unit := do
    let ctx ← read

    let unchanged old newParserState : BaseIO Unit :=
      -- when syntax is unchanged, reuse command processing task as is
      -- NOTE: even if the syntax tree is functionally unchanged, the new parser state may still
      -- have changed because of trailing whitespace and comments etc., so it is passed separately
      -- from `old`
      if let some oldNext := old.nextCmdSnap? then do
        let newProm ← IO.Promise.new
        -- can reuse range, syntax unchanged
        BaseIO.chainTask (sync := true) old.finishedSnap.task fun oldFinished =>
          -- also wait on old command parse snapshot as parsing is cheap and may allow for
          -- elaboration reuse
          BaseIO.chainTask (sync := true) oldNext.task fun oldNext => do
            let cancelTk ← IO.CancelToken.new
            parseCmd oldNext newParserState oldFinished.cmdState newProm sync cancelTk ctx
        prom.resolve <| { old with nextCmdSnap? := some {
          stx? := none
          reportingRange? := some ⟨newParserState.pos, ctx.input.endPos⟩
          task := newProm.result! } }
      else prom.resolve old  -- terminal command, we're done!

    -- fast path, do not even start new task for this snapshot (see [Incremental Parsing])
    if let some old := old? then
      if let some nextCom ← old.nextCmdSnap?.bindM (·.get?) then
        if let some nextNextCom ← nextCom.nextCmdSnap?.bindM (·.get?) then
          if (← isBeforeEditPos nextNextCom.parserState.pos) then
            return (← unchanged old old.parserState)

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
      if stx.eqWithInfo old.stx then
        -- Here we must make sure to pass the *new* parser state; see NOTE in `unchanged`
        return (← unchanged old parserState)
      -- On first change, immediately cancel old invocation for all subsequent commands. This
      -- includes setting the global parse cancellation token, which is stored in
      -- `next?` below. Thus we can be sure that no further commands will start to elaborate in the
      -- old invocation from this point on.
      old.nextCmdSnap?.forM (·.cancelRec)
      -- For the current command, we depend on the elaborator to either reuse parts of `old` or
      -- cancel them as soon as reuse can be ruled out.

    -- check for cancellation, most likely during elaboration of previous command, before starting
    -- processing of next command
    if (← parseCancelTk.isSet) then
      if let some old := old? then
        -- all of `old` is discarded, so cancel all of it
        toSnapshotTree old |>.children.forM (·.cancelRec)

      -- this is a bit ugly as we don't want to adjust our API with `Option`s just for cancellation
      -- (as no-one should look at this result in that case) but anything containing `Environment`
      -- is not `Inhabited`
      prom.resolve <| {
        diagnostics := .empty, stx := .missing, parserState
        elabSnap := default
        finishedSnap := .finished none { diagnostics := .empty, cmdState }
        reportSnap := default
        nextCmdSnap? := none
      }
      return

    -- Start new task when leaving fast-forwarding path; see "General notes" above
    let _ ← (if sync then BaseIO.asTask else (.pure <$> ·)) do
      -- definitely resolved in `doElab` task
      let elabPromise ← IO.Promise.new
      let finishedPromise ← IO.Promise.new
      let reportPromise ← IO.Promise.new
      let minimalSnapshots := internal.cmdlineSnapshots.get cmdState.scopes.head!.opts
      let (stx', parserState') := if minimalSnapshots && !Parser.isTerminalCommand stx then
        (default, default)
      else
        (stx, parserState)
      -- report terminal tasks on first line of decl such as not to hide incremental tactics'
      -- progress
      let initRange? := getNiceCommandStartPos? stx |>.map fun pos => ⟨pos, pos⟩
      let finishedSnap := {
        stx? := stx'
        reportingRange? := initRange?
        task := finishedPromise.result!
      }
      let next? ← if Parser.isTerminalCommand stx then pure none
        -- for now, wait on "command finished" snapshot before parsing next command
        else some <$> IO.Promise.new
      let nextCmdSnap? := next?.map ({
        stx? := none
        reportingRange? := some ⟨parserState.pos, ctx.input.endPos⟩
        cancelTk? := parseCancelTk
        task := ·.result!
      })
      let diagnostics ← Snapshot.Diagnostics.ofMessageLog msgLog

      -- use per-command cancellation token for elaboration so that
      let elabCmdCancelTk ← IO.CancelToken.new
      prom.resolve {
        diagnostics, finishedSnap, nextCmdSnap?
        stx := stx', parserState := parserState'
        elabSnap := { stx? := stx', task := elabPromise.result!, cancelTk? := some elabCmdCancelTk }
        reportSnap := { stx? := none, reportingRange? := initRange?, task := reportPromise.result! }
      }
      let cmdState ← doElab stx cmdState beginPos
        { old? := old?.map fun old => ⟨old.stx, old.elabSnap⟩, new := elabPromise }
        finishedPromise elabCmdCancelTk ctx
      let traceTask ←
        if (← isTracingEnabledForCore `Elab.snapshotTree cmdState.scopes.head!.opts) then
          -- We want to trace all of `CommandParsedSnapshot` but `traceTask` is part of it, so let's
          -- create a temporary snapshot tree containing all tasks but it
          let snaps := #[
            { stx? := stx', task := elabPromise.result!.map (sync := true) toSnapshotTree },
            { stx? := stx', task := finishedPromise.result!.map (sync := true) toSnapshotTree }] ++
            cmdState.snapshotTasks
          let tree := SnapshotTree.mk { diagnostics := .empty } snaps
          BaseIO.bindTask (← tree.waitAll) fun _ => do
            let .ok (_, s) ← EIO.toBaseIO <| tree.trace |>.run
              { ctx with options := cmdState.scopes.head!.opts } { env := cmdState.env }
              | pure <| .pure <| .mk { diagnostics := .empty } #[]
            let mut msgLog := MessageLog.empty
            for trace in s.traceState.traces do
              msgLog := msgLog.add {
                fileName := ctx.fileName
                severity := MessageSeverity.information
                pos      := ctx.fileMap.toPosition beginPos
                data     := trace.msg
              }
            return .pure <| .mk { diagnostics := (← Snapshot.Diagnostics.ofMessageLog msgLog) } #[]
        else
          pure <| .pure <| .mk { diagnostics := .empty } #[]
      reportPromise.resolve <|
        .mk { diagnostics := .empty } <|
          cmdState.snapshotTasks.push {
            stx? := none
            reportingRange? := initRange?
            task := traceTask
          }
      if let some next := next? then
        -- We're definitely off the fast-forwarding path now
        parseCmd none parserState cmdState next (sync := false) elabCmdCancelTk ctx

  doElab (stx : Syntax) (cmdState : Command.State) (beginPos : String.Pos)
      (snap : SnapshotBundle DynamicSnapshot) (finishedPromise : IO.Promise CommandFinishedSnapshot)
      (cancelTk : IO.CancelToken) : LeanProcessingM Command.State := do
    let ctx ← read
    let scope := cmdState.scopes.head!
    -- reset per-command state
    let cmdStateRef ← IO.mkRef { cmdState with
      messages := .empty, traceState := {}, snapshotTasks := #[] }
    let cmdCtx : Elab.Command.Context := { ctx with
      cmdPos       := beginPos
      snap?        := if internal.cmdlineSnapshots.get scope.opts then none else snap
      cancelTk?    := some cancelTk
    }
    let (output, _) ←
      IO.FS.withIsolatedStreams (isolateStderr := Core.stderrAsMessages.get scope.opts) do
        EIO.toBaseIO do
          withLoggingExceptions
            (getResetInfoTrees *> Elab.Command.elabCommandTopLevel stx)
            cmdCtx cmdStateRef
    let cmdState ← cmdStateRef.get
    let mut messages := cmdState.messages
    if !output.isEmpty then
      messages := messages.add {
        fileName := ctx.fileName
        severity := MessageSeverity.information
        pos      := ctx.fileMap.toPosition beginPos
        data     := output
      }
    let cmdState : Command.State := { cmdState with messages }
    let mut reportedCmdState := cmdState
    -- definitely resolve eventually
    snap.new.resolve <| .ofTyped { diagnostics := .empty : SnapshotLeaf }

    let infoTree : InfoTree := cmdState.infoState.trees[0]!
    let cmdline := internal.cmdlineSnapshots.get scope.opts && !Parser.isTerminalCommand stx
    if cmdline then
      -- discard all metadata apart from the environment; see `internal.cmdlineSnapshots`
      reportedCmdState := { env := reportedCmdState.env, maxRecDepth := 0 }
    finishedPromise.resolve {
      diagnostics := (← Snapshot.Diagnostics.ofMessageLog cmdState.messages)
      infoTree? := infoTree
      traces := cmdState.traceState
      cmdState := reportedCmdState
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
  let cancelTk ← IO.CancelToken.new
  process.parseCmd (old?.map (·.2)) parserState commandState prom (sync := true) cancelTk
    |>.run (old?.map (·.1))
    |>.run { inputCtx with }
  return prom.result!

/-- Waits for and returns final command state, if importing was successful. -/
partial def waitForFinalCmdState? (snap : InitialSnapshot) : Option Command.State := do
  let snap ← snap.result?
  let snap ← snap.processedSnap.get.result?
  goCmd snap.firstCmdSnap.get
where goCmd snap :=
  if let some next := snap.nextCmdSnap? then
    goCmd next.get
  else
    snap.finishedSnap.get.cmdState

end Lean
