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
See `Lean.PostprocessTraces`.
-/

public section

namespace Lean.PostprocessTraces

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

end Lean.PostprocessTraces

namespace Lean.Elab.PostprocessTraces

open Lean.PostprocessTraces Command

/--
Decomposes the synthetic container message produced by `addTraceAsMessages`
(``.tagged `trace <| .trace _ _ roots``, possibly inside context wrappers) into its trace roots,
together with a function that reassembles the container from transformed roots.
-/
meta partial def traceContainer? (data : MessageData) :
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
meta def postprocessMessage (post : TracePostprocessor) (msg : Message) :
    CoreM (Option Message) := do
  let some (rebuild, roots) := traceContainer? msg.data
    | return some msg
  let roots ← post (roots.map TraceTree.ofMessageData)
  if roots.isEmpty then
    return none
  return some { msg with data := rebuild (roots.map (·.toMessageData)) }

/--
Runs a command and returns all messages (sync and async) it produces, clearing the snapshot
tasks after collection so that async messages are not reported twice. The surrounding message
log is unaffected; it is restored even if the command is interrupted.
-/
meta def runAndCollectMessages (cmd : Syntax) : CommandElabM (Array Message) := do
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
meta def evalPostprocessorTopLevel (post : Term) : CommandElabM TracePostprocessor := do
  let savedTrace := (← get).traceState
  try
    runTermElabM fun _ => evalPostprocessor post
  finally
    modify fun st => { st with traceState := savedTrace }

end Lean.Elab.PostprocessTraces
