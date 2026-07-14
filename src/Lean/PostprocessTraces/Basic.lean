/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public meta import Lean.Elab.Command
public meta import Lean.Meta.Eval
import Lean.CoreM

/-!
# Experimental: Trace Postprocessors and the `postprocess_traces` Command

Trace messages of complex elaboration tasks can be very large, and finding the relevant part in
the editor requires a lot of clicking and searching. This module provides trace postprocessors:
functions that transform the trace of a command before it is reported, e.g. by filtering out
irrelevant subtrees, hoisting the interesting ones, or pre-expanding the paths to matches.

A trace postprocessor (`Lean.PostprocessTraces.TracePostprocessor`) receives the array of trace roots of
one trace message and returns the transformed roots. The `Lean.PostprocessTraces` namespace provides a
small set of operations (`filterSubtrees`, `hoist`, `exposeSubtrees`, `countNodes`, `selfTime`)
that compose left-to-right with `>=>`. The selecting operations take a pattern
(`Lean.PostprocessTraces.TracePattern`), a predicate on trace subtrees; built-in patterns select by trace
class (`ofClass`), text (`containsString`), result (`succeeded`, `failed`, `errored`,
`unsuccessful`), and time (`minTimeMs`, `minSelfTimeMs`). Users can define
their own postprocessors and patterns as ordinary functions.

Syntax:
`postprocess_traces post in cmd` transforms the trace messages produced by `cmd` with `post`.

Traces are stored as `MessageData` (see `MessageData.trace`); `TraceTree` is a structured view of
such messages that takes care of the context wrappers (`MessageData.withContext` etc.) around
trace nodes.
-/

public section

namespace Lean.PostprocessTraces

/--
Experimental. `postprocess_traces` and the library around it are expected to change in the future.

`postprocess_traces post in cmd` runs `cmd` and transforms every trace message it produces
with the trace postprocessor `post : Lean.PostprocessTraces.TracePostprocessor` before it is reported.

The postprocessor receives the array of trace roots of each trace message and returns the
transformed roots; returning an empty array drops the message entirely. The `Lean.PostprocessTraces`
namespace (automatically opened in `post`) provides operations such as `filterSubtrees`, `hoist`,
`exposeSubtrees`, and `selfTime`, which take patterns such as `ofClass`, `containsString`, and
`minTimeMs` and compose left-to-right with `>=>`. User-defined postprocessors and patterns are
ordinary functions.

For example, the following only shows the instance-synthesis steps that mention `tryResolve`,
together with their ancestors:
```lean
set_option trace.Meta.synthInstance true in
postprocess_traces filter (containsString "tryResolve") in
example : Inhabited (List Nat) := inferInstance
```
-/
scoped syntax (name := postprocessTracesCmd)
  "postprocess_traces " term " in" ppLine command : command

/--
A structured view of a trace message (`MessageData.trace`), used by trace postprocessors
(see `TracePostprocessor`).
-/
inductive TraceTree where
  /--
  A trace node `[data.cls] msg` with the given children.

  `wrap` restores the context wrappers (`MessageData.withContext` etc.) that were peeled off the
  original `MessageData` while decomposing it; it is re-applied around the node by
  `toMessageData`.
  -/
  | node (data : TraceData) (msg : MessageData) (children : Array TraceTree)
      (wrap : MessageData → MessageData)
  /-- A child message that is not itself a trace node (e.g. produced by `addRawTrace`). -/
  | leaf (msg : MessageData)

instance : Inhabited TraceTree := ⟨.leaf .nil⟩

/--
Decomposes trace `MessageData` into a `TraceTree`. The `MessageData` can be reconstructed using
`TraceTree.toMessageData`.
-/
meta partial def TraceTree.ofMessageData (msg : MessageData) : TraceTree :=
  go id msg
where
  go (wrap : MessageData → MessageData) : MessageData → TraceTree
    | .withContext ctx m => go (fun m => wrap (.withContext ctx m)) m
    | .withNamingContext ctx m => go (fun m => wrap (.withNamingContext ctx m)) m
    | .trace data m children => .node data m (children.map (go id)) wrap
    | m => .leaf (wrap m)

/-- Reassembles the `MessageData` of a trace tree. -/
meta partial def TraceTree.toMessageData : TraceTree → MessageData
  | .node data msg children wrap => wrap (.trace data msg (children.map toMessageData))
  | .leaf msg => msg

/--
A trace postprocessor transforms the trace roots of a trace message before it is reported,
e.g. by filtering out irrelevant subtrees or pre-expanding interesting nodes.
Returning an empty array drops the trace message entirely.

Traces are reported as one message per source range inside a command, and a postprocessor is
applied to each of these messages separately; it therefore cannot move trace roots from one
source range to another.

Postprocessors are applied by the `postprocess_traces post in cmd` command and can be composed
left-to-right with `>=>`.
-/
abbrev TracePostprocessor := Array TraceTree → CoreM (Array TraceTree)

instance : Inhabited TracePostprocessor := ⟨fun roots => return roots⟩

/--
Decomposes the synthetic container message produced by `addTraceAsMessages`
(``.tagged `trace <| .trace _ _ roots``, possibly inside context wrappers) into its trace roots,
together with a function that reassembles the container from transformed roots.
-/
private meta partial def traceContainer? (data : MessageData) :
    Option ((Array MessageData → MessageData) × Array MessageData) :=
  go id data
where
  go (wrap : MessageData → MessageData) :
      MessageData → Option ((Array MessageData → MessageData) × Array MessageData)
    | .withContext ctx m       => go (fun m => wrap (.withContext ctx m)) m
    | .withNamingContext ctx m => go (fun m => wrap (.withNamingContext ctx m)) m
    | .tagged n (.trace data head children) =>
      if n == `trace then
        some (fun children => wrap (.tagged n (.trace data head children)), children)
      else
        none
    | _ => none

/--
Applies `post` to a trace message (see `addTraceAsMessages`), returning `none` if the
postprocessor dropped all roots of the message. Non-trace messages are returned unchanged.
-/
private meta def postprocessMessage (post : TracePostprocessor) (msg : Message) :
    CoreM (Option Message) := do
  let some (rebuild, roots) := traceContainer? msg.data
    | return some msg
  let roots ← post (roots.map TraceTree.ofMessageData)
  if roots.isEmpty then
    return none
  return some { msg with data := rebuild (roots.map (·.toMessageData)) }

end Lean.PostprocessTraces

namespace Lean.Elab.PostprocessTraces
open Lean.PostprocessTraces Command

/--
Runs a command and returns all messages (sync and async) it produces, clearing the snapshot
tasks after collection so that async messages are not reported twice. The surrounding message
log is unaffected; it is restored even if the command is interrupted.
-/
private meta def runAndCollectMessages (cmd : Syntax) : CommandElabM (Array Message) := do
  let saved := (← get).messages
  -- `elabCommandTopLevel` resets the info state; save the trees recorded so far (e.g. for the
  -- postprocessor term) so that hovers and completions keep working
  let savedTrees := (← get).infoState.trees
  modify fun st => { st with messages := {} }
  try
    -- do not forward the snapshot as we don't want messages assigned to it to leak outside
    withReader ({ · with snap? := none }) do
      elabCommandTopLevel cmd
    let msgs := (← get).messages ++
      (← get).snapshotTasks.foldl (· ++ ·.get.getAll.foldl (· ++ ·.diagnostics.msgLog) .empty) .empty
    modify fun st => { st with snapshotTasks := #[], messages := {} }
    return msgs.toArray
  finally
    modify fun st => { st with
      infoState.trees := savedTrees ++ st.infoState.trees
      messages        := saved ++ st.messages }

/--
Evaluates a term of type `TracePostprocessor`, with the `Lean.PostprocessTraces` namespace opened so
that the built-in operations and patterns are available unqualified.
-/
private meta def evalPostprocessor (post : Term) : TermElabM TracePostprocessor := do
  let post ← `(open Lean.PostprocessTraces in ($post : TracePostprocessor))
  let type := mkConst ``TracePostprocessor
  withoutModifyingEnv do
    let e ← Term.elabTermEnsuringType post type
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    -- on elaboration errors, abort before `evalExpr` reports a redundant `sorryAx` error
    if e.hasSyntheticSorry then
      throwAbortTerm
    if (← Term.logUnassignedUsingErrorInfos (← Meta.getMVars e)) then
      throwAbortTerm
    -- the cast in `evalExpr` is sound: `e` was elaborated at `type`, which denotes the type
    -- argument `TracePostprocessor`
    unsafe Meta.evalExpr TracePostprocessor type e

/--
Evaluates the postprocessor without leaking the traces produced by elaborating the postprocessor
term itself into the (typically trace-enabled) surrounding context.
-/
private meta def evalPostprocessorTopLevel (post : Term) : CommandElabM TracePostprocessor := do
  let savedTrace := (← get).traceState
  try
    runTermElabM fun _ => evalPostprocessor post
  finally
    modify fun st => { st with traceState := savedTrace }

@[command_elab Lean.PostprocessTraces.postprocessTracesCmd]
meta def elabPostprocessTraces : CommandElab
  | `(command| postprocess_traces $post in $cmd) => do
    -- on errors in `post`, log them and fall back to the identity postprocessor so that `cmd`
    -- still elaborates, e.g. while the postprocessor term is being edited
    let post ← try
      evalPostprocessorTopLevel post
    catch ex =>
      logException ex
      pure fun roots => return roots
    for msg in ← runAndCollectMessages cmd do
      try
        if let some msg ← liftCoreM <| postprocessMessage post msg then
          modify fun st => { st with messages := st.messages.add msg }
      catch ex =>
        -- if the postprocessor fails at runtime, report the message unprocessed
        logException ex
        modify fun st => { st with messages := st.messages.add msg }
  | _ => throwUnsupportedSyntax

end Lean.Elab.PostprocessTraces

namespace Lean.PostprocessTraces

/--
A pattern selects the trace subtrees that an operation acts on (see `filter`, `hoist`, and
`expand`). Patterns are ordinary predicates: the built-in ones (such as `containsString`,
`unsuccessful`, or `minTimeMs`) can be combined with custom conditions in a `fun`.
-/
abbrev TracePattern := TraceTree → CoreM Bool

namespace TraceTree

/-- The `TraceData` of a trace node; `none` for leaf messages. -/
def data? : TraceTree → Option TraceData
  | .node data .. => some data
  | .leaf _       => none

/-- The trace class of a trace node; `none` for leaf messages. -/
def cls? (t : TraceTree) : Option Name :=
  t.data?.map (·.cls)

/-- The children of this tree. -/
def children : TraceTree → Array TraceTree
  | .node _ _ children _ => children
  | .leaf _              => #[]

/-- Replaces the children of a trace node. Leaf messages are returned unchanged. -/
def withChildren (t : TraceTree) (children : Array TraceTree) : TraceTree :=
  match t with
  | .node data msg _ wrap => .node data msg children wrap
  | .leaf msg             => .leaf msg

/-- Transforms the `TraceData` of a trace node. Leaf messages are returned unchanged. -/
def modifyData (t : TraceTree) (f : TraceData → TraceData) : TraceTree :=
  match t with
  | .node data msg children wrap => .node (f data) msg children wrap
  | .leaf msg                    => .leaf msg

/-- Elapsed time of this node in seconds; `0` if no profiling data is available. -/
def elapsed (t : TraceTree) : Float :=
  match t.data? with
  | some data => data.stopTime - data.startTime
  | none      => 0

/--
Elapsed time of this node that is not accounted for by its children, in seconds; `0` if no
profiling data is available.
-/
def selfElapsed (t : TraceTree) : Float :=
  max 0 (t.elapsed - t.children.foldl (fun s c => s + c.elapsed) 0)

/--
The message of this node (without its children), formatted as a string.
Useful for text-based filters but expensive.
-/
def headText : TraceTree → BaseIO String
  | .node data msg _ wrap => do
    let s ← (wrap msg).toString
    return match data.result? with
      | some r => s!"{r.toEmoji} {s}"
      | none   => s
  | .leaf msg => msg.toString

/-- The `TraceResult` of a trace node; `none` for leaf messages and nodes without a result. -/
def result? (t : TraceTree) : Option TraceResult :=
  t.data?.bind (·.result?)

/--
Collects all maximal subtrees satisfying `p` in `acc`: adds `t` itself if `p t` holds, and
otherwise recurses into the children. Matching subtrees are not searched for nested matches.
-/
partial def collectSubtrees (p : TracePattern) (t : TraceTree)
    (acc : Array TraceTree := #[]) : CoreM (Array TraceTree) := do
  if ← p t then
    return acc.push t
  t.children.foldlM (fun acc c => collectSubtrees p c acc) acc

/--
Prunes the tree to the subtrees satisfying `p`, keeping their ancestors for context; `none` if
there is no match. The resulting tree consists of those nodes that either have a matching
ancestor or transitive child. Matching subtrees are not searched for nested matches.
-/
partial def filterSubtrees (p : TracePattern) (t : TraceTree) :
    CoreM (Option TraceTree) := do
  if ← p t then
    return some t
  let children ← t.children.filterMapM (filterSubtrees p)
  if children.isEmpty then
    return none
  return some (t.withChildren children)

end TraceTree

private def containsSubstr (s pat : String) : Bool :=
  (s.find? pat).isSome

section TracePatterns

/-- Matches the trace nodes with the exact trace class `cls`. -/
def ofClass (cls : Name) : TracePattern := fun t =>
  return t.cls? == some cls

/--
Matches the subtrees whose trace class or head message contains `pat` as a substring.
For large traces, this is an expensive pattern because all head messages need to be
pretty-printed; to select nodes by their exact trace class, prefer the much cheaper `ofClass`.
-/
def containsString (pat : String) : TracePattern := fun t => do
  if (t.cls?.map (·.toString)).any (containsSubstr · pat) then
    return true
  return containsSubstr (← t.headText) pat

/--
Matches the trace nodes whose action succeeded (✅️, `TraceResult.success`).
Nodes without a recorded result (e.g. from `addTrace`) do not match.
-/
def succeeded : TracePattern := fun t =>
  return t.result? == some .success

/-- Matches the trace nodes whose action failed (❌️, `TraceResult.failure`). -/
def failed : TracePattern := fun t =>
  return t.result? == some .failure

/-- Matches the trace nodes whose action threw an exception (💥️, `TraceResult.error`). -/
def errored : TracePattern := fun t =>
  return t.result? == some .error

/--
Matches the trace nodes whose action did not succeed, i.e. failed (❌️) or threw an exception
(💥️). Nodes without a recorded result (e.g. from `addTrace`) do not match.
-/
def unsuccessful : TracePattern := fun t =>
  return t.result? == some .failure || t.result? == some .error

/--
Matches the subtrees whose action took at least `ms` milliseconds.
Timing information is only available with `set_option trace.profiler true`.
-/
def minTimeMs (ms : Float) : TracePattern := fun t =>
  return t.elapsed * 1000 ≥ ms

/--
Matches the subtrees whose action took at least `ms` milliseconds outside of their child nodes.
Timing information is only available with `set_option trace.profiler true`.
-/
def minSelfTimeMs (ms : Float) : TracePattern := fun t =>
  return t.selfElapsed * 1000 ≥ ms

end TracePatterns

section Postprocessors

/--
Keeps only the subtrees matching `p`, together with their ancestors for context; all other nodes
are removed. Matching subtrees are kept in their entirety and not searched for nested matches
(see `TraceTree.filterSubtrees`).
-/
def filterSubtrees (p : TracePattern) : TracePostprocessor := fun roots =>
  roots.filterMapM (·.filterSubtrees p)

/--
Hoists the subtrees matching `p` to the top level, so that every new trace root is a match;
ancestors and unrelated subtrees are discarded. Matches nested inside other matches are not
searched for.
-/
def hoist (p : TracePattern) : TracePostprocessor := fun roots =>
  roots.foldlM (fun acc t => t.collectSubtrees p acc) #[]

/--
Expands all transitive ancestors of the subtrees matching `p` in the editor, so that the trace
opens already showing all matches. No nodes are removed, and all other nodes, including the
matches themselves, keep their expansion state. Matching subtrees are not searched for nested
matches.
-/
partial def exposeSubtrees (p : TracePattern) : TracePostprocessor := fun roots =>
  roots.mapM fun root => return (← go root).1
where
  /-- Returns the transformed tree and whether it contains a match. -/
  go (t : TraceTree) : CoreM (TraceTree × Bool) := do
    if ← p t then return (t, true)
    let results ← t.children.mapM go
    let hasMatchBelow := results.any (·.2)
    let t := t.withChildren (results.map (·.1))
    let t := if hasMatchBelow then t.modifyData ({ · with collapsed := false }) else t
    return (t, hasMatchBelow)

/-- Appends the number of nodes inside each subtree to the subtree's head message. -/
partial def countNodes : TracePostprocessor := fun roots =>
  return roots.map fun root => (go root).1
where
  /-- Returns the transformed tree and its number of nodes. -/
  go : TraceTree → TraceTree × Nat
    | .leaf msg => (.leaf msg, 1)
    | .node data msg children wrap =>
      let results := children.map go
      let n := results.foldl (fun n (_, k) => n + k) 1
      let suffix := if n == 1 then "" else "s"
      (.node data m!"{msg} ({n} node{suffix})" (results.map (·.1)) wrap, n)

/-- Formats a duration in milliseconds with one decimal place, e.g. `12.3ms`. -/
private def formatMs (ms : Float) : String :=
  let tenths := (ms * 10).round.toUInt64.toNat
  s!"{tenths / 10}.{tenths % 10}ms"

/--
Appends the number of milliseconds spent inside each subtree but outside of its child nodes to
the subtree's head message. Timing information is only available with
`set_option trace.profiler true`; nodes without it are not annotated.
-/
partial def selfTime : TracePostprocessor := fun roots =>
  return roots.map go
where
  go : TraceTree → TraceTree
    | .leaf msg => .leaf msg
    | t@(.node data msg children wrap) =>
      let msg :=
        if data.startTime == 0 then msg
        else m!"{msg} (self: {formatMs (t.selfElapsed * 1000)})"
      .node data msg (children.map go) wrap

end Postprocessors

end Lean.PostprocessTraces
