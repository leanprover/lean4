/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Joachim Breitner
-/
module

prelude
import Init.Try
import Lean.Linter.Basic
import Lean.Server.InfoUtils
import Lean.Elab.Tactic.Try
import Lean.Elab.Tactic.Meta
import Lean.Elab.BuiltinTerm

/-! # Auto-`try?`

After a command is elaborated, walk its info trees and run `try?` at positions of interest --
empty `by` blocks, terminal tactics that left goals unsolved, and `sorry` tactics -- to
surface suggestions for completing the proof. Each trigger is gated by its own option:
`autoTry.onEmptyProof`, `autoTry.onUnsolvedGoal`, `autoTry.onSorry`. The infotree walk is
attached to the linter hook (`addLinter`), but the feature is not a "linter" in the user-
facing sense; it just borrows that hook to find a convenient post-elaboration entry point.

Two heuristics decide when *not* to fire:

1. Tactic positions that were elaborated against more than one proof state are skipped:
   a single "Try this" suggestion can't replay against multiple goals. This catches the rhs
   of `<;>` (run once per subgoal via the `focus / all_goals` expansion), `repeat`/`repeat'`,
   `iterate`, and similar.

2. The whole hook stays silent on commands that logged any error other than an "unsolved
   goals" error. If the user is in the middle of fixing a broken proof we don't want to
   distract them with suggestions.
-/

namespace Lean.Elab.Tactic.AutoTry

open Lean Elab Term Tactic Command Try Meta

/--
Run `try?` on empty proofs (e.g. empty `by`, empty `· `, empty `case h => `).
-/
register_builtin_option autoTry.onEmptyProof : Bool := {
  defValue := false
  descr := "run `try?` on empty proofs and empty subproofs and report any suggestions"
}

/--
Former name of `autoTry.onEmptyProof`. Kept as an alias so that `set_option
tactic.tryOnEmptyBy true` in code written against earlier releases continues to enable
the empty-`by` suggestion. Use `autoTry.onEmptyProof` in new code.
-/
register_builtin_option tactic.tryOnEmptyBy : Bool := {
  defValue := false
  descr := "deprecated alias for `autoTry.onEmptyProof`"
  deprecation? := some {
    since := "2026-06-29"
    text? := some "use `autoTry.onEmptyProof` instead"
  }
}

/--
Run `try?` whenever there are unsolved goals (and not other errors).
-/
register_builtin_option autoTry.onUnsolvedGoal : Bool := {
  defValue := false
  descr := "run `try?` on each proof or subproof that left a goal unsolved and report \
    any suggestions"
}

/--
Run `try?` on each `sorry` tactic.
-/
register_builtin_option autoTry.onSorry : Bool := {
  defValue := false
  descr := "run `try?` on each `sorry` tactic and report any suggestions"
}

/--
When enabled, autoTry logs an info message for each emitted suggestion describing the
text-edit it represents: the source range to replace and the literal replacement text.
Intended for tests: the [apply] widget normally hides the separator characters that the
edit inserts, so without this option there is no way for `#guard_msgs` to verify the
exact text being inserted on click.
-/
register_builtin_option debug.autoTry.showEdits : Bool := {
  defValue := false
  descr := "if set, autoTry logs an info message per emitted suggestion showing the edit's \
    source range and the literal replacement text (for testing the widget data)"
}

builtin_initialize registerTraceClass `autoTry

/--
Run a `MetaM` computation in a saved elaboration scope (`env`, `mctx`, `lctx`, `opts`,
`currNamespace`, `openDecls`), propagating any messages and traces back into the
surrounding `CommandElabM` state. The surrounding cancel token is forwarded so that
long-running `try?` calls get cancelled when the linter snapshot is cancelled.
-/
def runMetaMInScope (env : Environment) (mctx : MetavarContext) (lctx : LocalContext)
    (opts : Options) (namingCtx : NamingContext) (x : MetaM α) : CommandElabM α := do
  let cmdCtx ← read
  -- `try?` may create temporary auxiliary declarations during library search; running with
  -- a non-exporting environment keeps any such declarations from leaking out as exports.
  let env := env.setExporting false
  let core : CoreM α := Prod.fst <$> x.run { lctx } { mctx }
  let (res, newCoreState) ←
    (withOptions (fun _ => opts) core).toIO
      { currNamespace := namingCtx.currNamespace, openDecls := namingCtx.openDecls
        fileName := cmdCtx.fileName, fileMap := cmdCtx.fileMap
        cancelTk? := cmdCtx.cancelTk? }
      { env, ngen := {} }
  modify fun s => { s with
    messages := s.messages ++ newCoreState.messages
    traceState.traces := s.traceState.traces ++ newCoreState.traceState.traces }
  return res

def isSorryTactic (stx : Syntax) : Bool :=
  match stx.getKind with
  | `Lean.Parser.Tactic.tacticSorry | `Lean.Parser.Tactic.tacticAdmit => true
  | _ => false

/-- Which kind of auto-`try?` trigger this is. -/
inductive TriggerKind
  /-- A proof or subproof that left a goal unsolved (detected by walking the message
  log for `Tactic.unsolvedGoals` errors). `tacticSeq` is the body to append to,
  `insertPos` is the position at which to insert the new tactic. The dedup key for
  filtering multi-state replays (rhs of `<;>` etc.) is the source range of the
  underlying message, which lives on the candidate's `ref` syntax. -/
  | unsolvedGoal (tacticSeq : Syntax) (insertPos : String.Pos.Raw)
  /-- A `sorry` tactic. The suggestion *replaces* the `sorry`. -/
  | sorryTactic

/--
Compute the separator string to insert between the existing tail of a `tacticSeq` and a
new appended tactic. Heuristic:
* Empty `tacticSeq`: `" "` (just a space; the parser will normalise leading whitespace).
* Non-empty `tacticSeq` whose first and last tactics live on different source lines:
  newline followed by spaces aligning with the first tactic.
* Otherwise (non-empty single-line `tacticSeq`): `"; "`.

This is a heuristic and gets various edge cases wrong (mixed-indentation bodies, comments
between tactics, etc.). It should be replaced by a proper formatter once one is available.
-/
def computeAppendSep (tacticSeq : Syntax) (fileMap : FileMap) : String := Id.run do
  -- Locate the first tactic of the body; absence means an empty `tacticSeq`.
  let some bodyStart := tacticSeq.getPos? | return " "
  let some bodyEnd := tacticSeq.getTailPos? | return " "
  let startPos := fileMap.toPosition bodyStart
  let endPos := fileMap.toPosition bodyEnd
  if startPos.line == endPos.line then
    return "; "
  return "\n" ++ String.ofList (List.replicate startPos.column ' ')

/--
Build a synthetic atom with zero textual content whose syntactic range is the empty
range `[p, p)`. Used as the `origSpan?` for append-style suggestions so the IDE inserts
the replacement text at `p` without overwriting anything.
-/
def mkEmptyRangeStx (p : String.Pos.Raw) : Syntax :=
  Syntax.atom (.original "".toRawSubstring p "".toRawSubstring p) ""

/-- Build a synthetic atom whose source range matches `range`. Used as the
`addSuggestion ref` argument so the "Try this:" diagnostic appears at exactly the
same source range as the underlying "unsolved goals" error. -/
def mkRangeStx (range : Lean.Syntax.Range) : Syntax :=
  Syntax.atom (.original "".toRawSubstring range.start "".toRawSubstring range.stop) ""

/--
A trigger candidate: enough info for the hook to drive `try?` and emit a suggestion
without re-walking the infotree.

`env`, `mctx`, `opts`, `namingCtx` carry the elaboration scope active when the trigger
fired; for unsolved-goal triggers this is recovered from the `MessageData.withContext` /
`MessageData.withNamingContext` wrappers the log machinery attaches, and so includes
any `withTheReader Core.Context` overrides (e.g. from term-level `open … in <term>`).
For `sorry` triggers it's derived from the surrounding `TacticInfo`'s `ContextInfo`.

`ref` is the "Try this:" diagnostic anchor *and* the dedup key for the multi-state
filter -- a synthetic atom matching the message range for unsolved-goal triggers, or
the `sorry` tactic syntax itself for sorry triggers (which is also what the
suggestion replaces).
-/
structure Candidate where
  kind : TriggerKind
  ref : Syntax
  env : Environment
  mctx : MetavarContext
  opts : Options
  namingCtx : NamingContext
  goal : MVarId

/--
Walk a `MessageData` tree, collecting each `MessageData.ofGoal mvarId` together with the
elaboration contexts wrapped around it: the innermost `MessageDataContext` (carrying
`env`, `mctx`, `lctx`, `opts`) and the innermost `NamingContext` (carrying
`currNamespace`, `openDecls`). -/
partial def collectGoalsAndCtxFromMessage (msg : MessageData) :
    Array (MessageDataContext × NamingContext × MVarId) := go none none msg #[]
where
  go (mc? : Option MessageDataContext) (nc? : Option NamingContext)
      (msg : MessageData) (acc : Array _) := match msg with
    | .withContext c msg         => go (some c) nc? msg acc
    | .withNamingContext n msg   => go mc? (some n) msg acc
    | .nest _ msg | .group msg   => go mc? nc? msg acc
    | .tagged _ msg              => go mc? nc? msg acc
    | .compose a b               => go mc? nc? b (go mc? nc? a acc)
    | .ofWidget _ alt            => go mc? nc? alt acc
    | .trace _ msg children      =>
      children.foldl (init := go mc? nc? msg acc) (fun acc m => go mc? nc? m acc)
    | .ofGoal mvarId             =>
      match mc?, nc? with
      | some mc, some nc => acc.push (mc, nc, mvarId)
      | _, _             => acc
    | _                          => acc

/--
Locate the tactic-sequence body in `cmd` "responsible" for an `unsolved goals` error
at `range`. Returns `(body, insertPos)` where `body` is the null-node holding the
tactics (used for separator computation) and `insertPos` is where to append a new
tactic.

Strategy: descend along the path of nodes whose range contains `range`, then take
the outermost seq-variant in the smallest containing node's subtree -- handling both
the case where the error is logged inside the body (`case h => skip`, `{ skip }`,
`· skip`) and the case where it's logged at an adjacent token (`by` keyword for
`by skip`, the synthetic case-body marker, etc.).

The only syntax-kind knowledge is `tacticSeq1Indented` vs `tacticSeqBracketed`,
needed to read the tactics-container at child index 0 vs 1 and to know that the
empty-body insertion point sits before `}` (for bracketed) or right after the
opening token (for indented -- the message range's `stop` is a reliable proxy).

These two kinds are the complete universe of tactic-sequence variants in the parser:
`tacticSeq` (`def tacticSeq := tacticSeqBracketed <|> tacticSeq1Indented`) and
`tacticSeqIndentGt` are pure wrappers that descend into one of the two real forms,
and `walkAndFind` pierces them transparently via DFS. New seq variants would have
to be added here; the silent-skip is reported via the call-site trace. -/
partial def findTacticSeqBody (cmd : Syntax) (range : Lean.Syntax.Range) :
    Option (Syntax × String.Pos.Raw) :=
  walkAndFind cmd
where
  /- If `stx` is a recognised seq-variant, returns the tactics-container null-node
     together with the insertion position for appending a new tactic. For non-empty
     bodies that's the body's tail; for empty bodies it's just before `}` (bracketed)
     or the message range's `stop` (indented -- just past the wrapper's opening token). -/
  seqBodyAndInsertPos? (stx : Syntax) : Option (Syntax × String.Pos.Raw) :=
    match stx.getKind with
    | ``Lean.Parser.Tactic.tacticSeq1Indented =>
      let body := stx[0]
      some (body, body.getTailPos?.getD range.stop)
    | ``Lean.Parser.Tactic.tacticSeqBracketed =>
      let body := stx[1]
      some (body, body.getTailPos?.getD (stx[2].getPos?.getD range.stop))
    | _ => none
  walkAndFind (stx : Syntax) : Option (Syntax × String.Pos.Raw) := Id.run do
    let some r := stx.getRange? | return none
    unless r.includes range do return none
    for child in stx.getArgs do
      if let some result := walkAndFind child then return some result
    outermostSeqInSubtree stx
  outermostSeqInSubtree (stx : Syntax) : Option (Syntax × String.Pos.Raw) := Id.run do
    if let some result := seqBodyAndInsertPos? stx then return some result
    for child in stx.getArgs do
      if let some result := outermostSeqInSubtree child then return some result
    return none

/--
Collect candidate trigger points.

* **Unsolved-goal triggers** come from the command's message log. For each
  `Tactic.unsolvedGoals` error, `collectGoalsAndCtxFromMessage` recovers the
  elaboration scope and goal mvarids, and `findTacticSeqBody` locates the enclosing
  `by` / `{ … }` / `· ` / `case` scope's body and insertion position from the
  command syntax.
* **Sorry triggers** are read directly off `sorry`-tactic info-tree nodes.
-/
def collectTriggerPoints (cmd : Syntax) (opts : Options) (tree : InfoTree)
    (msgs : PersistentArray Message) : CommandElabM (Array Candidate) := do
  let onEmpty := autoTry.onEmptyProof.get opts || tactic.tryOnEmptyBy.get opts
  let onUnsolved := autoTry.onUnsolvedGoal.get opts
  let onSorry := autoTry.onSorry.get opts
  let mut acc : Array Candidate := #[]
  -- Sorry triggers still come from the info tree, since they're per-`sorry`-token.
  if onSorry then
    acc := tree.foldInfo (init := acc) fun ctx info acc => Id.run do
      if let .ofTacticInfo tacInfo := info then
        if isSorryTactic tacInfo.stx then
          if let some goal := tacInfo.goalsBefore.head? then
            let namingCtx : NamingContext :=
              { currNamespace := ctx.currNamespace, openDecls := ctx.openDecls }
            return acc.push {
              kind := .sorryTactic, ref := tacInfo.stx,
              env := ctx.env, mctx := tacInfo.mctxBefore, opts := ctx.options,
              namingCtx, goal }
      return acc
  -- Unsolved-goal triggers come from the message log.
  if onUnsolved || onEmpty then
    let fileMap ← getFileMap
    let some cmdRange := cmd.getRange? (canonicalOnly := true) | return acc
    -- Dedup key is `(message range, goal mvarid)`: same range + same mvarid is a true
    -- duplicate (`runLintersAsync` merges the snapshot tree's diagnostics into the
    -- command state's message log, so the same `Tactic.unsolvedGoals` error may appear
    -- twice in `msgs`); same range + different mvarids is the genuinely distinct case
    -- that the downstream `<;>` filter needs to see (e.g. `tac <;> ·` re-enters the same
    -- empty cdot once per subgoal, each with its own goal).
    let mut seen : Std.HashSet (Lean.Syntax.Range × MVarId) := {}
    for msg in msgs do
      unless msg.severity matches .error do continue
      unless msg.data.hasTag (· == `Tactic.unsolvedGoals) do continue
      let some endPos := msg.endPos | continue
      let msgRange : Lean.Syntax.Range :=
        { start := fileMap.ofPosition msg.pos, stop := fileMap.ofPosition endPos }
      unless cmdRange.includes msgRange do continue
      let some (body, insertPos) := findTacticSeqBody cmd msgRange
        | trace[autoTry] "no tacticSeq body found for unsolved-goals message at \
            {msgRange.start.byteIdx}-{msgRange.stop.byteIdx}; \
            unrecognised seq variant?"
          continue
      let isEmpty := body.getPos?.isNone
      unless onUnsolved || (onEmpty && isEmpty) do continue
      let ref := mkRangeStx msgRange
      let goals := collectGoalsAndCtxFromMessage msg.data
      if goals.isEmpty then
        trace[autoTry] "Tactic.unsolvedGoals message yielded no (msgCtx, namingCtx, goal) \
          tuples; producer not following the `withContext`/`withNamingContext` contract?"
      for (msgCtx, namingCtx, mvarId) in goals do
        if seen.contains (msgRange, mvarId) then continue
        seen := seen.insert (msgRange, mvarId)
        acc := acc.push {
          kind := .unsolvedGoal body insertPos, ref,
          env := msgCtx.env, mctx := msgCtx.mctx, opts := msgCtx.opts,
          namingCtx, goal := mvarId }
  return acc

/--
Drive `try?` from `CommandElabM`, returning the suggestion array. Runs
`Try.collectTryCoreSuggestions` on `goal` inside the captured elaboration scope.
Returns `#[]` on error or interruption (control-flow exceptions are re-raised).
-/
def collectSuggestionsForGoal (c : Candidate) : CommandElabM (Array (TSyntax `tactic)) := do
  let some decl := c.mctx.decls.find? c.goal | return #[]
  runMetaMInScope c.env c.mctx decl.lctx c.opts c.namingCtx do
    let tacticAct : TacticM (Array (TSyntax `tactic)) := do
      try
        Try.collectTryCoreSuggestions {}
      catch e =>
        if e.isInterrupt || e.isMaxRecDepth then throw e
        trace[autoTry] "try? raised: {e.toMessageData}"
        return #[]
    -- Unfold `TacticM` (= `ReaderT Context (StateRefT State TermElabM)`) by hand to
    -- run `tacticAct` and recover its return value; `Tactic.run` would only let us
    -- get the leftover goals, not the `α`.
    let term : TermElabM (Array (TSyntax `tactic)) := withSynthesize do
      c.goal.withContext <|
        (tacticAct.run { elaborator := .anonymous }).run' { goals := [c.goal] }
    try Prod.fst <$> term.run {} {}
    catch e =>
      if e.isInterrupt || e.isMaxRecDepth then throw e
      trace[autoTry] "term elab raised: {e.toMessageData}"
      return #[]

/--
Emit a "Try these:" message whose code-action edits *append* each suggestion to the end
of `byStx`'s tactic sequence (or just after `by` for an empty body). The `messageData?`
override keeps the rendered widget text clean (no leading separator). `cmdLine` is the
1-based line of the enclosing command's start, used to render edit positions relative to
the command (so tests are robust to moving the example up or down the file).
-/
def emitAppendSuggestions (tacticSeq ref : Syntax) (insertPos : String.Pos.Raw)
    (suggs : Array (TSyntax `tactic)) (cmdLine : Nat) : CommandElabM Unit := do
  if suggs.isEmpty then return
  let fileMap ← getFileMap
  let sep := computeAppendSep tacticSeq fileMap
  let origSpan := mkEmptyRangeStx insertPos
  let showEdits := debug.autoTry.showEdits.get (← getOptions)
  let formatted ← suggs.mapM fun tac => do
    let fmt ← liftCoreM <| PrettyPrinter.ppTactic tac
    let cleanText := fmt.pretty
    -- The widget display uses `messageData?` (the bare tactic) while the actual edit
    -- text in `suggestion` carries the leading separator -- this keeps the [apply]
    -- line readable without losing the appending semantics on click.
    let editText := sep ++ cleanText
    if showEdits then
      let pos := fileMap.toPosition insertPos
      let dLine := pos.line - cmdLine + 1  -- match `#guard_msgs (positions := true)`: +N:COL
      logInfoAt ref
        m!"autoTry edit: insert {repr editText} at +{dLine}:{pos.column}"
    return ({
      suggestion := .string editText
      messageData? := some (toMessageData tac)
      toCodeActionTitle? := some (fun _ => "Try this: " ++ cleanText)
    } : Tactic.TryThis.Suggestion)
  liftCoreM <|
    if formatted.size == 1 then
      Tactic.TryThis.addSuggestion ref formatted[0]! (origSpan? := origSpan)
    else
      Tactic.TryThis.addSuggestions ref formatted (origSpan? := origSpan)

/--
Run `try?` by elaborating its tactic syntax against `goal` and letting `try?` emit its
own "Try this:" message anchored at `tk`. `try?`'s default emission replaces the syntax
at the current ref, which is exactly what we want for the `sorry` trigger.
-/
def runReplaceTryOnGoal (c : Candidate) : CommandElabM Unit := do
  let some decl := c.mctx.decls.find? c.goal | return
  runMetaMInScope c.env c.mctx decl.lctx c.opts c.namingCtx do
    try
      let tryStx ← `(tactic| try?)
      withRef c.ref do
        discard <| Lean.Elab.runTactic c.goal tryStx
    catch e =>
      if e.isInterrupt || e.isMaxRecDepth then throw e
      trace[autoTry] "try? raised: {e.toMessageData}"

/--
Returns `true` if the message log contains any error within `stxRange` that is *not* an
"unsolved goals" error. Used to skip the auto-`try?` hook on commands the user is in the
middle of fixing -- suggestions for the unsolved goal are not useful while other errors
need to be addressed first.
-/
def hasNonUnsolvedGoalError (stx : Syntax) : CommandElabM Bool := do
  let some range := stx.getRange? | return false
  let fileMap := (← read).fileMap
  let msgs := (← get).messages
  return msgs.reportedPlusUnreported.any fun m =>
    let inRange := range.contains (fileMap.ofPosition m.pos) (includeStop := true)
    let isError := m.severity matches .error
    let isUnsolved := m.data.hasTag (· == `Tactic.unsolvedGoals)
    inRange && isError && !isUnsolved

/--
Returns `true` iff a suggestion may safely be inserted at the candidate's insertion
point -- i.e., iff a tactic typed there would run on exactly one clearly-identified
goal. Uses `InfoTree.goalsAt?`, the same runtime-state query the LSP
`getInteractiveGoals` request drives:

* Exactly one `TacticInfo` runtime instance covers the insertion point. If two
  instances reach the same position (`<;>` re-entered its rhs against different
  goal states, etc.), suppress -- the appended tactic would run for each of them.
* Reading off that instance the state the newly-inserted tactic would actually
  run against: `goalsBefore` for `sorry` (the suggestion replaces the `sorry`)
  and for empty bodies (the suggestion is the first thing to run in the body);
  `goalsAfter` for non-empty bodies (the suggestion runs after the existing
  tactics). That state must have exactly one goal.
-/
def singleGoalAtInsertPos (tree : InfoTree) (fileMap : FileMap) (c : Candidate) : Bool :=
  let hoverPos := match c.kind with
    | .unsolvedGoal _ insertPos => insertPos
    | .sorryTactic              => c.ref.getPos?.getD 0
  match tree.goalsAt? fileMap hoverPos with
  | [r] =>
    let targetGoals := match c.kind with
      | .unsolvedGoal tacticSeq _ =>
        if tacticSeq.getPos?.isSome then r.tacticInfo.goalsAfter
        else r.tacticInfo.goalsBefore
      | .sorryTactic => r.tacticInfo.goalsBefore
    targetGoals.length == 1
  | _ => false

/--
The auto-`try?` post-elaboration hook.

Plugged into the linter machinery (`addLinter`) because that's a convenient post-command-
elab entry point with infotree access. The feature itself is *not* a linter: it does not
bail on `messages.hasErrors`, since the triggers we care about (empty `by`, unsolved
goals, `sorry`) all produce errors or warnings of their own.
-/
def autoTryHook : Linter where run := withSetOptionIn fun stx => do
  let opts ← getOptions
  let onEmpty := autoTry.onEmptyProof.get opts || tactic.tryOnEmptyBy.get opts
  let onUnsolved := autoTry.onUnsolvedGoal.get opts
  let onSorry := autoTry.onSorry.get opts
  unless onEmpty || onUnsolved || onSorry do return
  if ← hasNonUnsolvedGoalError stx then
    trace[autoTry] "skipping: command has non-unsolved-goal errors"
    return
  trace[autoTry] "running: onEmpty={onEmpty} onUnsolved={onUnsolved} onSorry={onSorry}"
  let fileMap := (← read).fileMap
  let cmdLine := (fileMap.toPosition (stx.getPos?.getD 0)).line
  let msgs := (← get).messages.reportedPlusUnreported
  let trees ← getInfoTrees
  for tree in trees do
    let candidates ← collectTriggerPoints stx opts tree msgs
    trace[autoTry] "trigger points: {candidates.size}"
    for c in candidates do
      unless singleGoalAtInsertPos tree fileMap c do
        trace[autoTry] "suppressed: InfoView at insert point does not show exactly one \
          goal state with one goal"
        continue
      match c.kind with
      | .unsolvedGoal tacticSeq insertPos =>
        let suggs ← collectSuggestionsForGoal c
        emitAppendSuggestions tacticSeq c.ref insertPos suggs cmdLine
      | .sorryTactic =>
        runReplaceTryOnGoal c

builtin_initialize addLinter autoTryHook

end Lean.Elab.Tactic.AutoTry
