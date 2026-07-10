/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Lean.Elab.Command
import Lean.Elab.Eval
import Init.Data.String.Search  -- needed for `String.find?`/`String.replace`
import Init.Data.String.TakeDrop  -- needed for `String.take`

/-!
# Trace postprocessors: `trace_view`, `store_trace_as`, `#trace_roots`, `#trace_view`

Trace messages of complex elaboration tasks can be very large, and finding the relevant part in
the editor requires a lot of clicking and searching. This module provides trace postprocessors:
functions that transform the trace of a command before it is reported, e.g. by filtering out
irrelevant subtrees, focusing on a single trace class, or pre-expanding the paths to failures.

A trace postprocessor (`Lean.TraceView.TracePostprocessor`) receives the array of trace roots of
one trace message and returns the transformed roots. The `Lean.TraceView` namespace provides basic
combinators (`focusOn`, `hideSucceeded`, `maxDepth`, `minTimeMs`, `grep`, `expandMatches`,
`expandAll`, `collapseAll`, `expandFailures`, `onRoots`, …); users can define their own
postprocessors as ordinary functions and compose them with `>=>`.

Syntax:
`trace_view post in cmd` transforms the trace messages produced by `cmd` with `post`.

Traces are stored as `MessageData` (see `MessageData.trace`); `TraceTree` is a structured view of
such messages that takes care of the context wrappers (`MessageData.withContext` etc.) around
trace nodes.
-/

public section

namespace Lean.TraceView

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

namespace TraceTree

/--
Decomposes trace `MessageData` into a `TraceTree`. The `MessageData` can be reconstructed using
`TraceTree.toMessageData`.
-/
partial def ofMessageData (msg : MessageData) : TraceTree :=
  go id msg
where
  go (wrap : MessageData → MessageData) : MessageData → TraceTree
    | .withContext ctx m       => go (fun m => wrap (.withContext ctx m)) m
    | .withNamingContext ctx m => go (fun m => wrap (.withNamingContext ctx m)) m
    | .trace data m children   => .node data m (children.map (go id)) wrap
    | m                        => .leaf (wrap m)

/-- Reassembles the `MessageData` of a trace tree. -/
partial def toMessageData : TraceTree → MessageData
  | .node data msg children wrap => wrap (.trace data msg (children.map toMessageData))
  | .leaf msg                    => msg

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
The message of this node (without its children), formatted as a string.
Useful for text-based filters such as `grep`.
-/
def headText : TraceTree → BaseIO String
  | .node data msg _ wrap => do
    let s ← (wrap msg).toString
    return match data.result? with
      | some r => s!"{r.toEmoji} {s}"
      | none   => s
  | .leaf msg => msg.toString

/-- Whether this node itself represents a failed action (`TraceResult.failure` or `.error`). -/
def isFailure (t : TraceTree) : Bool :=
  match t.data?.bind (·.result?) with
  | some .failure | some .error => true
  | _                           => false

/-- Whether this node or any transitive child represents a failed action. -/
partial def hasFailure (t : TraceTree) : Bool :=
  t.isFailure || t.children.any hasFailure

/-- The number of nodes in this tree (including the root and leaf messages). -/
partial def size (t : TraceTree) : Nat :=
  t.children.foldl (fun n c => n + c.size) 1

/--
Collects all maximal subtrees satisfying `p`: returns `t` itself if `p t`, and otherwise
recurses into the children.
-/
partial def collectSubtrees (p : TraceTree → Bool) (t : TraceTree)
    (acc : Array TraceTree := #[]) : Array TraceTree :=
  if p t then
    acc.push t
  else
    t.children.foldl (fun acc c => collectSubtrees p c acc) acc

/--
Prunes the tree to the subtrees satisfying `p`, keeping their ancestors for context.
The resulting tree consistes of those nodes that either have a matching ancestor or transitive
child.
-/
partial def filterSubtrees (p : TraceTree → BaseIO Bool) (t : TraceTree) :
    BaseIO (Option TraceTree) := do
  if ← p t then
    return some t
  let children ← t.children.filterMapM (filterSubtrees p)
  if children.isEmpty then
    return none
  return some (t.withChildren children)

/-- Sets the `TraceData.collapsed` flag on this node and all transitive children. -/
partial def setCollapsedAll (t : TraceTree) (collapsed : Bool) : TraceTree :=
  t.modifyData ({ · with collapsed }) |>.withChildren (t.children.map (setCollapsedAll · collapsed))

end TraceTree

/--
A trace postprocessor transforms the trace roots of a trace message before it is reported,
e.g. by filtering out irrelevant subtrees or pre-expanding interesting nodes.
Returning an empty array drops the trace message entirely.

Traces are reported as one message per source range inside a command, and a postprocessor is
applied to each of these messages separately; it therefore cannot move trace roots from one
source range to another.
TODO: Really?

Postprocessors are applied by the `trace_view post in cmd` and `#trace_view t post` commands and
can be composed left-to-right with `>=>`.
-/
abbrev TracePostprocessor := Array TraceTree → CoreM (Array TraceTree)

instance : Inhabited TracePostprocessor := ⟨fun roots => return roots⟩

private def containsSubstr (s pat : String) : Bool :=
  (s.find? pat).isSome

/--
Keeps only the subtrees whose trace class is `cls`. Matches nested inside other trace roots are
hoisted to the top level.
-/
def focusOn (cls : Name) : TracePostprocessor := fun roots =>
  return roots.foldl (fun acc t => t.collectSubtrees (·.cls? == some cls) acc) #[]

/--
Folds every successful subtree that contains no failure into a single line, keeping the paths to
failed actions fully visible. Trace roots without any failure are folded into their root node.
-/
partial def hideSucceeded : TracePostprocessor := fun roots =>
  return roots.map go
where
  go (t : TraceTree) : TraceTree :=
    if t.hasFailure then
      t.withChildren (t.children.map go)
    else
      t.withChildren #[]

/-- Truncates all trace trees below the given depth (`maxDepth 0` keeps only the roots). -/
def maxDepth (depth : Nat) : TracePostprocessor := fun roots =>
  return roots.map (go depth)
where
  go : Nat → TraceTree → TraceTree
    | 0,         t => t.withChildren #[]
    | depth + 1, t => t.withChildren (t.children.map (go depth))

/--
Keeps only the nodes that took at least `ms` milliseconds, and their ancestors for context.
Timing information is only available with `set_option trace.profiler true`.
-/
def minTimeMs (ms : Float) : TracePostprocessor := fun roots =>
  roots.filterMapM (·.filterSubtrees fun t => return t.elapsed * 1000 ≥ ms)

/--
Whether the trace class or head message of `t` contains `pat` as a substring.
For large traces, this is an expensive operation because all terms need to be pretty-printed.
-/
private def matchesPattern (pat : String) (t : TraceTree) : BaseIO Bool := do
  if (t.cls?.map (·.toString)).any (containsSubstr · pat) then
    return true
  return containsSubstr (← t.headText) pat

/--
Keeps only the subtrees whose trace class or head message contains `pat` as a substring, and
their ancestors for context.
For large traces, this is an expensive operation because all terms need to be pretty-printed.
-/
def grep (pat : String) : TracePostprocessor := fun roots =>
  roots.filterMapM (·.filterSubtrees (matchesPattern pat))

/--
Expands all transitive parents of the nodes whose trace class or head message contains `pat` as
a substring, so that the trace opens already showing all matches. Unlike `grep`, no nodes are
removed, and all other nodes, including the matches themselves, keep their expansion state.
For large traces, this is an expensive operation because all terms need to be pretty-printed.
-/
partial def expandMatches (pat : String) : TracePostprocessor := fun roots =>
  roots.mapM fun root => return (← go root).1
where
  /-- Returns the transformed tree and whether it contains a match. -/
  go (t : TraceTree) : BaseIO (TraceTree × Bool) := do
    let results ← t.children.mapM go
    let hasMatchBelow := results.any (·.2)
    let t := t.withChildren (results.map (·.1))
    let t := if hasMatchBelow then t.modifyData ({ · with collapsed := false }) else t
    return (t, hasMatchBelow || (← matchesPattern pat t))

/-- Expands all trace nodes in the editor by default. -/
def expandAll : TracePostprocessor := fun roots =>
  return roots.map (·.setCollapsedAll false)

/-- Collapses all trace nodes in the editor by default. -/
def collapseAll : TracePostprocessor := fun roots =>
  return roots.map (·.setCollapsedAll true)

/--
Expands all trace nodes on a path to a failed action in the editor by default, and collapses
everything else, so that the trace opens already showing the failures. No nodes are removed.
TODO: too inefficient; `hasFailure` is linear
-/
partial def expandFailures : TracePostprocessor := fun roots =>
  return roots.map go
where
  go (t : TraceTree) : TraceTree :=
    t.modifyData ({ · with collapsed := !t.hasFailure }) |>.withChildren (t.children.map go)

/--
Applies `post` to the trace roots selected by `sel`, leaving all other roots untouched.
This allows restricting a postprocessor to specific roots when a command produces many,
e.g. `onRoots (fun r => return r.cls? == some `Meta.synthInstance) hideSucceeded`.

The selected roots are postprocessed one at a time, so `post` cannot merge them.
-/
def onRoots (sel : TraceTree → CoreM Bool) (post : TracePostprocessor) : TracePostprocessor :=
  fun roots => roots.flatMapM fun root => do
    if ← sel root then post #[root] else return #[root]

/-- Applies `post` only to the trace roots of class `cls`, leaving all other roots untouched. -/
def onClass (cls : Name) (post : TracePostprocessor) : TracePostprocessor :=
  onRoots (fun root => return root.cls? == some cls) post

/--
Applies `post` only to the root with the given index (counting all trace roots of the command in
order, as displayed by `#trace_roots`), leaving all other roots untouched.

Note that for live `trace_view`, indices can shift whenever the traced command changes; for
traces stored with `store_trace_as`, they are stable.
-/
def onRootIdx (idx : Nat) (post : TracePostprocessor) : TracePostprocessor := fun roots => do
  let mut out := #[]
  for h : i in [0:roots.size] do
    if i == idx then
      out := out ++ (← post #[roots[i]])
    else
      out := out.push roots[i]
  return out

/--
Decomposes the synthetic container message produced by `addTraceAsMessages`
(`.tagged \`trace <| .trace _ _ roots`, possibly inside context wrappers) into its trace roots,
together with a function that reassembles the container from transformed roots.
-/
private partial def traceContainer? (data : MessageData) :
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
private def postprocessMessage (post : TracePostprocessor) (msg : Message) :
    CoreM (Option Message) := do
  let some (rebuild, roots) := traceContainer? msg.data
    | return some msg
  let roots ← post (roots.map TraceTree.ofMessageData)
  if roots.isEmpty then
    return none
  return some { msg with data := rebuild (roots.map (·.toMessageData)) }

end Lean.TraceView

namespace Lean.Elab.TraceView
open Lean.TraceView Command

/--
Runs a command and collects all messages (sync and async) it produces, clearing the snapshot
tasks after collection so that async messages are not reported twice. The message log is empty
when `cmd` starts; the caller is responsible for saving and restoring the surrounding log.
-/
private def runAndCollectMessages (cmd : Syntax) : CommandElabM (MessageLog × Array Message) := do
  let saved := (← get).messages
  modify fun st => { st with messages := {} }
  -- do not forward the snapshot as we don't want messages assigned to it to leak outside
  withReader ({ · with snap? := none }) do
    elabCommandTopLevel cmd
  let msgs := (← get).messages ++
    (← get).snapshotTasks.foldl (· ++ ·.get.getAll.foldl (· ++ ·.diagnostics.msgLog) .empty) .empty
  modify fun st => { st with snapshotTasks := #[], messages := {} }
  return (saved, msgs.toArray)

/--
Evaluates a term of type `TracePostprocessor`, with the `Lean.TraceView` namespace opened so
that the basic combinators are available unqualified.
-/
private unsafe def evalPostprocessor (post : Term) : TermElabM TracePostprocessor := do
  let post ← `(open Lean.TraceView in ($post : TracePostprocessor))
  Term.evalTerm TracePostprocessor (mkConst ``TracePostprocessor) post
-- TODO: the `post` syntax element should be hoverable, support autocompletion and hovers
-- TODO: Why is `evalTerm` unsafe? Should we use something else here?

/--
Evaluates the postprocessor without leaking the traces produced by elaborating the postprocessor
term itself into the (typically trace-enabled) surrounding context.
-/
private unsafe def evalPostprocessorTopLevel (post : Term) : CommandElabM TracePostprocessor := do
  let savedTrace := (← get).traceState
  try
    runTermElabM fun _ => evalPostprocessor post
  finally
    modify fun st => { st with traceState := savedTrace }

private unsafe def elabTraceViewUnsafe : CommandElab
  | `(command| trace_view $post in $cmd) => do
    let post ← evalPostprocessorTopLevel post
    let (saved, msgs) ← runAndCollectMessages cmd
    let mut out := saved
    for msg in msgs do
      if let some msg ← liftCoreM <| postprocessMessage post msg then
        out := out.add msg
    modify fun st => { st with messages := out }
  | _ => throwUnsupportedSyntax

@[implemented_by elabTraceViewUnsafe]
private opaque elabTraceViewImpl : CommandElab

@[builtin_command_elab Lean.TraceView.traceViewCmd] def elabTraceView : CommandElab :=
  elabTraceViewImpl

end Lean.Elab.TraceView
