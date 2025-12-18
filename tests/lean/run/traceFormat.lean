import Lean.CoreM

/-!
Tests formatting of traces in various combinations, on the cmdline automatically via `#guard_msgs`
and in the info view via manual testing.
-/

open Lean

def withNode (cls : Name) (msg : MessageData) (k : CoreM Unit) (collapsed := true) (tag := "") : CoreM Unit := do
  let oldTraces ← getTraces
  modifyTraces fun _ => {}
  k
  let ref ← getRef
  let mut data := { cls, collapsed, tag }
  let msg := .trace data msg ((← getTraces).toArray.map (·.msg))
  modifyTraces fun _ =>
    oldTraces.push { ref, msg }

/--
trace: [test] top-level leaf
[test] top-level leaf
[test] node with single leaf
  [test] leaf
[test] node with adjacent leafs
  [test] leaf
  [test] leaf
[test] nested nodes
  [test] leaf
  [test] node
    [test] leaf
  [test] leaf
[test] uncollapsed node
  [test] leaf
  [test] node
    [test] leaf
  [test] leaf
[test] node with nested newline
  [test] line1
      line2
-/
#guard_msgs in
#eval show CoreM Unit from do
  addTrace `test "top-level leaf"
  addTrace `test "top-level leaf"
  withNode `test "node with single leaf" do
    addTrace `test "leaf"
  withNode `test "node with adjacent leafs" do
    addTrace `test "leaf"
    addTrace `test "leaf"
  withNode `test "nested nodes" do
    addTrace `test "leaf"
    withNode `test "node" do
      addTrace `test "leaf"
    addTrace `test "leaf"
  withNode `test "uncollapsed node" (collapsed := false) do
    addTrace `test "leaf"
    withNode `test "node" do
      addTrace `test "leaf"
    addTrace `test "leaf"
  withNode `test "node with nested newline" do
    addTrace `test "line1\nline2"
