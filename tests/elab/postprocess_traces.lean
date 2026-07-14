module

meta import Lean.PostprocessTraces

/-!
Tests for trace postprocessors: the `postprocess_traces post in cmd` command, the built-in patterns and
operations in `Lean.PostprocessTraces`, and the fallback to the identity postprocessor on errors in the
postprocessor term.
-/

open scoped Lean.PostprocessTraces

-- `filter` keeps the matching subtrees plus their ancestors for context.
/--
trace: [Meta.synthInstance] ✅️ Inhabited (List Nat)
  [Meta.synthInstance.apply] ✅️ apply @instInhabitedList to Inhabited (List Nat)
    [Meta.synthInstance.tryResolve] ✅️ Inhabited (List Nat) ≟ Inhabited (List Nat)
-/
#guard_msgs in
set_option trace.Meta.synthInstance true in
postprocess_traces filterSubtrees (containsString "tryResolve") in
example : Inhabited (List Nat) := inferInstance

-- `hoist` makes the matching subtrees the new roots; `ofClass` selects nodes by their exact
-- trace class.
/-- trace: [Meta.synthInstance.instances] #[@instInhabitedOfMonad, @instInhabitedList] -/
#guard_msgs in
set_option trace.Meta.synthInstance true in
postprocess_traces hoist (ofClass `Meta.synthInstance.instances) in
example : Inhabited (List Nat) := inferInstance

-- Operations compose left-to-right with `>=>`.
/--
trace: [Meta.synthInstance.apply] ✅️ apply @instInhabitedList to Inhabited (List Nat)
  [Meta.synthInstance.tryResolve] ✅️ Inhabited (List Nat) ≟ Inhabited (List Nat)
-/
#guard_msgs in
set_option trace.Meta.synthInstance true in
postprocess_traces hoist (containsString "synthInstance.apply") >=> filterSubtrees (containsString "tryResolve") in
example : Inhabited (List Nat) := inferInstance

-- A postprocessor returning no roots drops the trace message entirely.
#guard_msgs in
set_option trace.Meta.synthInstance true in
postprocess_traces (fun _ => return #[]) in
example : Inhabited (List Nat) := inferInstance

/-!
The remaining operations and patterns are tested on synthetic trees so that node counts and
timings are deterministic. Times are given in seconds, as in `TraceData`.
-/

open Lean PostprocessTraces

private meta def mkTree (cls : Name) (msg : String) (kids : Array TraceTree := #[])
    (collapsed := true) (start : Float := 0) (stop : Float := 0)
    (result : Option TraceResult := none) : TraceTree :=
  .node { cls, collapsed, startTime := start, stopTime := stop, result? := result } m!"{msg}"
    kids id

private meta def runPost (post : TracePostprocessor) (roots : Array TraceTree) : Lean.CoreM Unit := do
  for root in (← post roots) do
    IO.println (← root.toMessageData.toString)

-- The generic trace formatter prints the elapsed seconds of profiled nodes in brackets after
-- the trace class.
private meta def timedTree : TraceTree :=
  mkTree `a "root" (start := 1.0) (stop := 1.1) #[
    mkTree `b "fast leaf" (start := 1.0) (stop := 1.03),
    mkTree `c "slow branch" (start := 1.03) (stop := 1.09) #[
      mkTree `d "grandchild" (start := 1.03) (stop := 1.05)]]

private meta def sampleTree : TraceTree :=
  mkTree `a "root" #[
    mkTree `b "mid" #[mkTree `c "the needle is here"],
    mkTree `d "other branch" #[mkTree `zeta "leaf"] (collapsed := false)
  ]

-- `selfTime` appends the time not accounted for by child nodes.
/--
info: [a] [0.100000] root (self: 10.0ms)
  [b] [0.030000] fast leaf (self: 30.0ms)
  [c] [0.060000] slow branch (self: 40.0ms)
    [d] [0.020000] grandchild (self: 20.0ms)
-/
#guard_msgs in
#eval runPost selfTime #[timedTree]

-- Nodes without profiling data are not annotated with times.
/-- info: [e] no timings -/
#guard_msgs in
#eval runPost selfTime #[mkTree `e "no timings"]

-- `countNodes` appends subtree sizes.
/--
info: [a] root (5 nodes)
  [b] mid (2 nodes)
    [c] the needle is here (1 node)
  [d] other branch (2 nodes)
    [zeta] leaf (1 node)
-/
#guard_msgs in
#eval runPost countNodes #[sampleTree]

-- `minSelfTimeMs` matches only `c` (40ms self time); `filter` keeps its ancestors and children.
/--
info: [a] [0.100000] root
  [c] [0.060000] slow branch
    [d] [0.020000] grandchild
-/
#guard_msgs in
#eval runPost (filterSubtrees (minSelfTimeMs 35)) #[timedTree]

-- Patterns are ordinary predicates and can combine built-in patterns with custom conditions.
/--
info: [a] [0.100000] root
  [c] [0.060000] slow branch
    [d] [0.020000] grandchild
-/
#guard_msgs in
#eval runPost (filterSubtrees fun t => return (← minTimeMs 50 t) && t.cls? != some `a) #[timedTree]

private meta def resultTree : TraceTree :=
  mkTree `a "root" #[
    mkTree `b "ok step" (result := some .success),
    mkTree `c "failed step" (result := some .failure),
    mkTree `d "error step" (result := some .error)]

-- `unsuccessful` matches both failed nodes and nodes that threw an exception; the root has no
-- recorded result and is only kept as an ancestor.
/--
info: [a] root
  [c] ❌️ failed step
  [d] 💥️ error step
-/
#guard_msgs in
#eval runPost (filterSubtrees unsuccessful) #[resultTree]

-- `failed` and `errored` distinguish the two unsuccessful results.
/--
info: [a] root
  [c] ❌️ failed step
-/
#guard_msgs in
#eval runPost (filterSubtrees failed) #[resultTree]

/-- info: [d] 💥️ error step -/
#guard_msgs in
#eval runPost (hoist errored) #[resultTree]

-- `succeeded` matches only successful nodes.
/-- info: [b] ✅️ ok step -/
#guard_msgs in
#eval runPost (hoist succeeded) #[resultTree]

/-!
`expand` only changes `TraceData.collapsed` flags, which are invisible in textual output, so we
test the flags directly.
-/

private meta partial def collapsedFlags (t : TraceTree) : String :=
  let state := if (t.data?.map (·.collapsed)).getD true then "closed" else "open"
  let head := s!"{t.cls?.getD .anonymous}:{state}"
  if t.children.isEmpty then head
  else head ++ "[" ++ ",".intercalate (t.children.map collapsedFlags).toList ++ "]"

-- The parents of the match open; the match itself stays closed, and the unrelated node `d`
-- keeps its (open) expansion state.
/-- info: "a:open[b:open[c:closed],d:open[zeta:closed]]" -/
#guard_msgs in
#eval show Lean.CoreM _ from do
  return collapsedFlags (← exposeSubtrees (containsString "needle") #[sampleTree])[0]!

-- Matching by trace class works too.
/-- info: "a:open[b:closed[c:closed],d:open[zeta:closed]]" -/
#guard_msgs in
#eval show Lean.CoreM _ from do
  return collapsedFlags (← exposeSubtrees (containsString "zeta") #[sampleTree])[0]!

-- Without a match, all expansion states are unchanged.
/-- info: "a:closed[b:closed[c:closed],d:open[zeta:closed]]" -/
#guard_msgs in
#eval show Lean.CoreM _ from do
  return collapsedFlags (← exposeSubtrees (containsString "no such text") #[sampleTree])[0]!

/-!
On errors in the postprocessor term, `postprocess_traces` logs the error and falls back to the identity
postprocessor, so the command still runs and reports its unmodified traces.
-/

/--
error: Unknown identifier `nonexistentPostprocessor`
---
trace: [debug] hello
-/
#guard_msgs in
set_option trace.debug true in
postprocess_traces nonexistentPostprocessor in
run_cmd trace[debug] "hello"

/--
error: Type mismatch
  "not a postprocessor"
has type
  String
but is expected to have type
  TracePostprocessor
---
trace: [debug] hello
-/
#guard_msgs in
set_option trace.debug true in
postprocess_traces "not a postprocessor" in
run_cmd trace[debug] "hello"

/-!
Robustness of the message pipeline: non-trace messages and messages logged by the postprocessor
itself must survive postprocessing, and runtime failures of the postprocessor must not lose the
traced command's output.
-/

-- Non-trace messages pass through the postprocessor unchanged.
/--
info: hi there
---
trace: [debug] hello
-/
#guard_msgs in
set_option trace.debug true in
postprocess_traces filterSubtrees (ofClass `debug) in
run_cmd do
  logInfo "hi there"
  trace[debug] "hello"

-- Messages logged by the postprocessor itself are kept.
/--
warning: postprocessor ran
---
trace: [debug] hello
-/
#guard_msgs in
set_option trace.debug true in
postprocess_traces (fun roots => do logWarning "postprocessor ran"; return roots) in
run_cmd trace[debug] "hello"

-- A postprocessor that throws at runtime is reported, and the affected message is shown
-- unprocessed.
/--
error: oh no
---
trace: [debug] hello
-/
#guard_msgs in
set_option trace.debug true in
postprocess_traces (fun _ => throwError "oh no") in
run_cmd trace[debug] "hello"
