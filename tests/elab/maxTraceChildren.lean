import Lean
/-!
Tests that `MessageData.format` (used for command-line output) truncates trace nodes according to
`maxTraceChildren`.
-/

open Lean

def mkTrace (n : Nat) : MessageData :=
  .trace { cls := `test } "parent" ((List.range n).toArray.map fun i => m!"child {i}")

/--
info: [test] parent
  child 0
  child 1
  child 2
  2 more entries... (increase `maxTraceChildren` to see more)
-/
#guard_msgs in
#eval show CoreM Unit from do
  let fmt ← (mkTrace 5).format (some { env := ← getEnv, mctx := {}, lctx := {}, opts := MessageData.maxTraceChildren.set {} 3 })
  IO.println fmt

/--
info: [test] parent
  child 0
  child 1
  child 2
-/
#guard_msgs in
#eval show CoreM Unit from do
  let fmt ← (mkTrace 3).format (some { env := ← getEnv, mctx := {}, lctx := {}, opts := MessageData.maxTraceChildren.set {} 3 })
  IO.println fmt

/--
info: [test] parent
  child 0
  child 1
  child 2
  child 3
  child 4
-/
#guard_msgs in
#eval show CoreM Unit from do
  let fmt ← (mkTrace 5).format (some { env := ← getEnv, mctx := {}, lctx := {}, opts := MessageData.maxTraceChildren.set {} 0 })
  IO.println fmt

/-! End-to-end: command-line style trace output is truncated too. -/

set_option maxTraceChildren 2 in
set_option trace.Meta.debug true in
/--
trace: [Meta.debug] ✅️ parent
  [Meta.debug] child 0
  [Meta.debug] child 1
  1 more entries... (increase `maxTraceChildren` to see more)
-/
#guard_msgs in
#eval show MetaM Unit from do
  withTraceNode `Meta.debug (fun _ => return "parent") do
    for i in [0:3] do
      trace[Meta.debug] "child {i}"
