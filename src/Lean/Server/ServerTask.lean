/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Huisinga
-/
prelude
import Init.System.IO

/-!
This file provides a thin `ServerTask` wrapper over the `Task` API.
All calls to the `Task` API in the language server should go through this API.

The reason for this API is that the elaborator consuming threads from the thread pool should
never hinder language server operations. Specifically, we want to ensure the following:
- All new tasks spawned in the language server must be dedicated so that they cannot be starved
  by the elaborator.
  - Dedicated tasks are costly, so avoid spawning new tasks for operations that are so cheap that
    they can just be done on the current thread instead.
- When mapping or binding a task:
  - If the function being mapped is sufficiently cheap that it can run on the current thread,
    map it with `sync := true`. This runs the function on the current thread if the task has already
    finished, or it reuses the thread of the task if the task has not finished.
    This ensures that the function to be executed cannot be starved by the elaborator.
  - If the function being mapped is not cheap / costly, map it with `prio := .dedicated`.
    This spawns a new thread and thus cannot be starved by the elaborator.
Finally, if the function being mapped is costly, but is already being executed in a dedicated task,
it is fine to pretend that it is a cheap function instead.

In request handlers, the distinction of whether an operation is "cheap" or "costly" should be
decided by the following:
- If the operation is sufficiently fast that it could run on the main task of the language server,
  blocking all other communication for a brief moment, then it can be considered cheap.
- If the operation is being executed in a dedicated task that isn't the main task of the server,
  it can also be considered cheap.
- Otherwise, it is to be considered costly.
-/

namespace Lean.Server

structure ServerTask (α : Type u) where
  task : Task α
  deriving Inhabited

instance : Coe (Task α) (ServerTask α) where
  coe := .mk

namespace ServerTask

def pure (x : α) : ServerTask α := Task.pure x

def get (t : ServerTask α) : α := t.task.get

def mapCheap (f : α → β) (t : ServerTask α) : ServerTask β :=
  t.task.map f (sync := true)

def mapCostly (f : α → β) (t : ServerTask α) : ServerTask β :=
  t.task.map f (prio := .dedicated)

def bindCheap (t : ServerTask α) (f : α → ServerTask β) : ServerTask β :=
  t.task.bind (f · |>.task) (sync := true)

def bindCostly (t : ServerTask α) (f : α → ServerTask β) : ServerTask β :=
  t.task.bind (f · |>.task) (prio := .dedicated)

namespace BaseIO

def asTask (act : BaseIO α) : BaseIO (ServerTask α) :=
  _root_.BaseIO.asTask (prio := .dedicated) act

def mapTaskCheap (f : α → BaseIO β) (t : ServerTask α) : BaseIO (ServerTask β) :=
  BaseIO.mapTask f t.task (sync := true)

def mapTaskCostly (f : α → BaseIO β) (t : ServerTask α) : BaseIO (ServerTask β) :=
  BaseIO.mapTask f t.task (prio := .dedicated)

def bindTaskCheap (t : ServerTask α) (f : α → BaseIO (ServerTask β)) : BaseIO (ServerTask β) :=
  BaseIO.bindTask t.task (ServerTask.task <$> f ·) (sync := true)

def bindTaskCostly (t : ServerTask α) (f : α → BaseIO (ServerTask β)) : BaseIO (ServerTask β) :=
  BaseIO.bindTask t.task (ServerTask.task <$> f ·) (prio := .dedicated)

end BaseIO

namespace EIO

def asTask (act : EIO ε α) : BaseIO (ServerTask (Except ε α)) :=
  _root_.EIO.asTask (prio := .dedicated) act

def mapTaskCheap (f : α → EIO ε β) (t : ServerTask α) : BaseIO (ServerTask (Except ε β)) :=
  EIO.mapTask f t.task (sync := true)

def mapTaskCostly (f : α → EIO ε β) (t : ServerTask α) : BaseIO (ServerTask (Except ε β)) :=
  EIO.mapTask f t.task (prio := .dedicated)

def bindTaskCheap (t : ServerTask α) (f : α → EIO ε (ServerTask (Except ε β))) : BaseIO (ServerTask (Except ε β)) :=
  EIO.bindTask t.task (ServerTask.task <$> f ·) (sync := true)

def bindTaskCostly (t : ServerTask α) (f : α → EIO ε (ServerTask (Except ε β))) : BaseIO (ServerTask (Except ε β)) :=
  EIO.bindTask t.task (ServerTask.task <$> f ·) (prio := .dedicated)

end EIO

namespace IO

def asTask (act : IO α) : BaseIO (ServerTask (Except IO.Error α)) :=
  _root_.IO.asTask (prio := .dedicated) act

def mapTaskCheap (f : α → IO β) (t : ServerTask α) : BaseIO (ServerTask (Except IO.Error β)) :=
  IO.mapTask f t.task (sync := true)

def mapTaskCostly (f : α → IO β) (t : ServerTask α) : BaseIO (ServerTask (Except IO.Error β)) :=
  IO.mapTask f t.task (prio := .dedicated)

def bindTaskCheap (t : ServerTask α) (f : α → IO (ServerTask (Except IO.Error β))) : BaseIO (ServerTask (Except IO.Error β)) :=
  IO.bindTask t.task (ServerTask.task <$> f ·) (sync := true)

def bindTaskCostly (t : ServerTask α) (f : α → IO (ServerTask (Except IO.Error β))) : BaseIO (ServerTask (Except IO.Error β)) :=
  IO.bindTask t.task (ServerTask.task <$> f ·) (prio := .dedicated)

end IO

def hasFinished (t : ServerTask α) : BaseIO Bool :=
  IO.hasFinished t.task

def waitAny (tasks : List (ServerTask α))
    (h : tasks.length > 0 := by exact Nat.zero_lt_succ _) : BaseIO α :=
  let ⟨tasks, h⟩ : { tasks : List (Task α) // tasks.length > 0 } :=
    ⟨tasks.map (·.task), by simpa⟩
  IO.waitAny tasks h

def cancel (t : ServerTask α) : BaseIO Unit :=
  IO.cancel t.task

end Lean.Server.ServerTask

def Task.asServerTask (t : Task α) : Lean.Server.ServerTask α := .mk t
