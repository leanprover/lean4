/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich

Additional `Task` definitions.
-/
module

prelude
public import Init.Core
public import Init.Data.List.Basic
public import Init.System.Promise

public section

/--
Waits until any of the tasks in the list has finished, then return its result.
-/
@[noinline]
def IO.waitAny (tasks : @& List (Task α)) (h : tasks.length > 0 := by exact Nat.zero_lt_succ _) :
    BaseIO α := do
  have : Nonempty α := ⟨tasks[0].get⟩
  let promise : IO.Promise α ← IO.Promise.new
  tasks.forM <| fun t => BaseIO.chainTask (sync := true) t promise.resolve
  return promise.result!.get

namespace Task

/--
Creates a task that, when all `tasks` have finished, computes the result of `f` applied to their
results.
-/
def mapList (f : List α → β) (tasks : List (Task α)) (prio := Task.Priority.default)
    (sync := false) : Task β :=
  go tasks []
where
  go
    | [], as =>
      if sync then
        .pure <| f as.reverse
      else
        Task.spawn (prio := prio) fun _ => f as.reverse
    | [t], as => t.map (fun a => f (a :: as).reverse) prio sync
    | t::ts, as => t.bind (fun a => go ts (a :: as)) prio sync
