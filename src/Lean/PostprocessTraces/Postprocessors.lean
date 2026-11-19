/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Lean.PostprocessTraces.Basic
import Lean.CoreM

public section

namespace Lean.PostprocessTraces

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
