/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Jared Roesch, Leonardo de Moura, Sebastian Ullrich, Mac Malone, Henrik Böving
-/
module

prelude
public import Init.System.IOError
public import Init.System.ST
public import Init.Data.Ord.Basic
import Init.Data.List.MapIdx

public section

open System

opaque IO.RealWorld.nonemptyType : NonemptyType.{0}
/--
A representation of “the real world” that's used in `IO` monads to ensure that `IO` actions are not
reordered.
-/
@[expose] def IO.RealWorld : Type := IO.RealWorld.nonemptyType.type

instance IO.RealWorld.instNonempty : Nonempty IO.RealWorld :=
  by exact IO.RealWorld.nonemptyType.property

/--
An `IO` monad that cannot throw exceptions.
-/
@[expose] def BaseIO (α : Type) := ST IO.RealWorld α

instance : Monad BaseIO := inferInstanceAs (Monad (ST IO.RealWorld))
instance : MonadFinally BaseIO := inferInstanceAs (MonadFinally (ST IO.RealWorld))

@[always_inline, inline]
def BaseIO.map (f : α → β) (x : BaseIO α) : BaseIO β :=
  f <$> x

/--
A monad that can have side effects on the external world or throw exceptions of type `ε`.

`BaseIO` is a version of this monad that cannot throw exceptions. `IO` sets the exception type to
`IO.Error`.
-/
/- TODO(Leo): mark it as an opaque definition. Reason: prevent
   functions defined in other modules from accessing `IO.RealWorld`.
   We don't want action such as
   ```
   def getWorld : IO (IO.RealWorld) := get
   ```
-/
@[expose] def EIO (ε : Type) (α : Type) : Type := EST ε IO.RealWorld α

/--
Runs a `BaseIO` action, which cannot throw an exception, in any other `EIO` monad.

This function is usually used implicitly via [automatic monadic
lifting](lean-manual://section/lifting-monads) rather being than called explicitly.
-/
@[always_inline, inline]
def BaseIO.toEIO (act : BaseIO α) : EIO ε α :=
  fun s => match act s with
  | .mk a s => .ok a s

instance : MonadLift BaseIO (EIO ε) := ⟨BaseIO.toEIO⟩

/--
Converts an `EIO ε` action that might throw an exception of type `ε` into an exception-free `BaseIO`
action that returns an `Except` value.
-/
@[always_inline, inline]
def EIO.toBaseIO (act : EIO ε α) : BaseIO (Except ε α) :=
  fun s => match act s with
  | .ok a s     => .mk (.ok a) s
  | .error ex s => .mk (.error ex) s

/--
Handles any exception that might be thrown by an `EIO ε` action, transforming it into an
exception-free `BaseIO` action.
-/
@[always_inline, inline]
def EIO.catchExceptions (act : EIO ε α) (h : ε → BaseIO α) : BaseIO α :=
  fun s => match act s with
  | .ok a s     => .mk a s
  | .error ex s => h ex s

instance : Monad (EIO ε) := inferInstanceAs (Monad (EST ε IO.RealWorld))
instance : MonadFinally (EIO ε) := inferInstanceAs (MonadFinally (EST ε IO.RealWorld))
instance : MonadExceptOf ε (EIO ε) := inferInstanceAs (MonadExceptOf ε (EST ε IO.RealWorld))
instance : OrElse (EIO ε α) := ⟨MonadExcept.orElse⟩
instance [Inhabited ε] : Inhabited (EIO ε α) := inferInstanceAs (Inhabited (EST ε IO.RealWorld α))

@[always_inline, inline]
def EIO.map (f : α → β) (x : EIO ε α) : EIO ε β :=
  f <$> x

@[always_inline, inline]
protected def EIO.throw (e : ε) : EIO ε α := throw e

@[always_inline, inline]
protected def EIO.tryCatch (x : EIO ε α) (handle : ε → EIO ε α) : EIO ε α :=
  MonadExceptOf.tryCatch x handle

/--
Converts an `Except ε` action into an `EIO ε` action.

If the `Except ε` action throws an exception, then the resulting `EIO ε` action throws the same
exception. Otherwise, the value is returned.
-/
@[always_inline, inline]
def EIO.ofExcept (e : Except ε α) : EIO ε α :=
  match e with
  | Except.ok a    => pure a
  | Except.error e => throw e

@[always_inline, inline]
def EIO.adapt (f : ε → ε') (m : EIO ε α) : EIO ε' α :=
  fun s => match m s with
  | .ok a s => .ok a s
  | .error e s => .error (f e) s

@[deprecated EIO.adapt (since := "2025-09-29"), always_inline, inline]
def EIO.adaptExcept (f : ε → ε') (m : EIO ε α) : EIO ε' α := EIO.adapt f m

open IO (Error) in
/--
A monad that supports arbitrary side effects and throwing exceptions of type `IO.Error`.
-/
abbrev IO : Type → Type := EIO Error

/--
Runs a `BaseIO` action, which cannot throw an exception, as an `IO` action.

This function is usually used implicitly via [automatic monadic
lifting](lean-manual://section/lifting-monads) rather than being called explicitly.
-/
@[inline] def BaseIO.toIO (act : BaseIO α) : IO α :=
  act

/--
Converts an `EIO ε` action into an `IO` action by translating any exceptions that it throws into
`IO.Error`s using `f`.
-/
@[inline] def EIO.toIO (f : ε → IO.Error) (act : EIO ε α) : IO α :=
  act.adapt f

/--
Converts an `EIO ε` action that might throw an exception of type `ε` into an exception-free `IO`
action that returns an `Except` value.
-/
@[inline] def EIO.toIO' (act : EIO ε α) : IO (Except ε α) :=
  act.toBaseIO

/--
Runs an `IO` action in some other `EIO` monad, using `f` to translate `IO` exceptions.
-/
@[inline] def IO.toEIO (f : IO.Error → ε) (act : IO α) : EIO ε α :=
  act.adapt f

/- After we inline `EState.run'`, the closed term `((), ())` is generated, where the second `()`
   represents the "initial world". We don't want to cache this closed term. So, we disable
   the "extract closed terms" optimization. -/
set_option compiler.extract_closed false in
/--
Executes arbitrary side effects in a pure context. This a **dangerous** operation that can easily
undermine important assumptions about the meaning of Lean programs, and it should only be used with
great care and a thorough understanding of compiler internals, and even then only to implement
observationally pure operations.

This function is not a good way to convert a `BaseIO α` into an `α`. Instead, use
[`do`-notation](lean-manual://section/do-notation).

Because the resulting value is treated as a side-effect-free term, the compiler may re-order,
duplicate, or delete calls to this function. The side effect may even be hoisted into a constant,
causing the side effect to occur at initialization time, even if it would otherwise never be called.
-/
@[noinline] unsafe def unsafeBaseIO (fn : BaseIO α) : α :=
  match fn (unsafeCast Unit.unit) with
  | .mk a _ => a

/--
Executes arbitrary side effects in a pure context, with exceptions indicated via `Except`. This a
**dangerous** operation that can easily undermine important assumptions about the meaning of Lean
programs, and it should only be used with great care and a thorough understanding of compiler
internals, and even then only to implement observationally pure operations.

This function is not a good way to convert an `EIO α` or `IO α` into an `α`. Instead, use
[`do`-notation](lean-manual://section/do-notation).

Because the resulting value is treated as a side-effect-free term, the compiler may re-order,
duplicate, or delete calls to this function. The side effect may even be hoisted into a constant,
causing the side effect to occur at initialization time, even if it would otherwise never be called.
-/
@[inline] unsafe def unsafeEIO (fn : EIO ε α) : Except ε α :=
  unsafeBaseIO fn.toBaseIO

@[inline, inherit_doc EIO] unsafe def unsafeIO (fn : IO α) : Except IO.Error α :=
  unsafeEIO fn


/--
Times the execution of an `IO` action.

The provided message `msg` and the time take are printed to the current standard error as a side
effect.
-/
@[extern "lean_io_timeit"] opaque timeit (msg : @& String) (fn : IO α) : IO α

@[extern "lean_io_allocprof"] opaque allocprof (msg : @& String) (fn : IO α) : IO α

/--
Returns `true` if and only if it is invoked during initialization.

Programs can execute `IO` actions during an initialization phase that occurs before the `main`
function is executed. The attribute `@[init <action>]` specifies which IO action is executed to set
the value of an opaque constant.
-/
@[extern "lean_io_initializing"] opaque IO.initializing : BaseIO Bool

namespace BaseIO

/--
Runs `act` in a separate `Task`, with priority `prio`.

Running the resulting `BaseIO` action causes the task to be started eagerly. Pure accesses to the
`Task` do not influence the impure `act`.

Unlike pure tasks created by `Task.spawn`, tasks created by this function will run even if the last
reference to the task is dropped. The `act` should explicitly check for cancellation via
`IO.checkCanceled` if it should be terminated or otherwise react to the last reference being
dropped.
-/
@[extern "lean_io_as_task"]
opaque asTask (act : BaseIO α) (prio := Task.Priority.default) : BaseIO (Task α) :=
  Task.pure <$> act

/--
Creates a new task that waits for `t` to complete and then runs the `BaseIO` action `f` on its
result. This new task has priority `prio`.

Running the resulting `BaseIO` action causes the task to be started eagerly. Unlike pure tasks
created by `Task.spawn`, tasks created by this function will run even if the last reference to the
task is dropped. The `act` should explicitly check for cancellation via `IO.checkCanceled` if it
should be terminated or otherwise react to the last reference being dropped.
-/
@[extern "lean_io_map_task"]
opaque mapTask (f : α → BaseIO β) (t : Task α) (prio := Task.Priority.default) (sync := false) :
    BaseIO (Task β) :=
  Task.pure <$> f t.get

/--
Creates a new task that waits for `t` to complete, runs the `IO` action `f` on its result, and then
continues as the resulting task. This new task has priority `prio`.

Running the resulting `BaseIO` action causes this new task to be started eagerly. Unlike pure tasks
created by `Task.spawn`, tasks created by this function will run even if the last reference to the
task is dropped. The `act` should explicitly check for cancellation via `IO.checkCanceled` if it
should be terminated or otherwise react to the last reference being dropped.
-/
@[extern "lean_io_bind_task"]
opaque bindTask (t : Task α) (f : α → BaseIO (Task β)) (prio := Task.Priority.default)
    (sync := false) : BaseIO (Task β) :=
  f t.get

/--
Creates a new task that waits for `t` to complete and then runs the `IO` action `f` on its result.
This new task has priority `prio`.

This is a version of `BaseIO.mapTask` that ignores the result value.

Running the resulting `BaseIO` action causes the task to be started eagerly. Unlike pure tasks
created by `Task.spawn`, tasks created by this function will run even if the last reference to the
task is dropped. The `act` should explicitly check for cancellation via `IO.checkCanceled` if it
should be terminated or otherwise react to the last reference being dropped.
-/
def chainTask (t : Task α) (f : α → BaseIO Unit) (prio := Task.Priority.default)
    (sync := false) : BaseIO Unit :=
  discard <| BaseIO.mapTask f t prio sync

/--
Creates a new task that waits for all the tasks in the list `tasks` to complete, and then runs the
`IO` action `f` on their results. This new task has priority `prio`.

Running the resulting `BaseIO` action causes the task to be started eagerly. Unlike pure tasks
created by `Task.spawn`, tasks created by this function will run even if the last reference to the
task is dropped. The `act` should explicitly check for cancellation via `IO.checkCanceled` if it
should be terminated or otherwise react to the last reference being dropped.
-/
def mapTasks (f : List α → BaseIO β) (tasks : List (Task α)) (prio := Task.Priority.default)
    (sync := false) : BaseIO (Task β) :=
  go tasks []
where
  go
    | [], as =>
      if sync then
        return .pure (← f as.reverse)
      else
        f as.reverse |>.asTask prio
    | [t], as => BaseIO.mapTask (fun a => f (a :: as).reverse) t prio sync
    | t::ts, as =>
      BaseIO.bindTask t (fun a => go ts (a :: as)) prio sync

end BaseIO

namespace EIO

/--
Runs `act` in a separate `Task`, with priority `prio`. Because `EIO ε` actions may throw an exception
of type `ε`, the result of the task is an `Except ε α`.

Running the resulting `IO` action causes the task to be started eagerly. Pure accesses to the `Task`
do not influence the impure `act`.

Unlike pure tasks created by `Task.spawn`, tasks created by this function will run even if the last
reference to the task is dropped. The `act` should explicitly check for cancellation via
`IO.checkCanceled` if it should be terminated or otherwise react to the last reference being
dropped.
-/
@[inline] def asTask (act : EIO ε α) (prio := Task.Priority.default) : BaseIO (Task (Except ε α)) :=
  act.toBaseIO.asTask prio

/--
Creates a new task that waits for `t` to complete and then runs the `IO` action `f` on its result.
This new task has priority `prio`.

Running the resulting `BaseIO` action causes the task to be started eagerly. Unlike pure tasks
created by `Task.spawn`, tasks created by this function will run even if the last reference to the
task is dropped. The `act` should explicitly check for cancellation via `IO.checkCanceled` if it
should be terminated or otherwise react to the last reference being dropped. Because `EIO ε` actions
may throw an exception of type `ε`, the result of the task is an `Except ε α`.
-/
@[inline] def mapTask (f : α → EIO ε β) (t : Task α) (prio := Task.Priority.default)
    (sync := false) : BaseIO (Task (Except ε β)) :=
  BaseIO.mapTask (fun a => f a |>.toBaseIO) t prio sync

/--
Creates a new task that waits for `t` to complete, runs the `EIO ε` action `f` on its result, and
then continues as the resulting task. This new task has priority `prio`.

Running the resulting `BaseIO` action causes this new task to be started eagerly. Unlike pure tasks
created by `Task.spawn`, tasks created by this function will run even if the last reference to the
task is dropped. The `act` should explicitly check for cancellation via `IO.checkCanceled` if it
should be terminated or otherwise react to the last reference being dropped. Because `EIO ε` actions
may throw an exception of type `ε`, the result of the task is an `Except ε α`.
-/
@[inline] def bindTask (t : Task α) (f : α → EIO ε (Task (Except ε β)))
    (prio := Task.Priority.default) (sync := false) : BaseIO (Task (Except ε β)) :=
  BaseIO.bindTask t (fun a => f a |>.catchExceptions fun e => return Task.pure <| Except.error e)
    prio sync

/--
Creates a new task that waits for `t` to complete and then runs the `EIO ε` action `f` on its result.
This new task has priority `prio`.

This is a version of `EIO.mapTask` that ignores the result value.

Running the resulting `EIO ε` action causes the task to be started eagerly. Unlike pure tasks
created by `Task.spawn`, tasks created by this function will run even if the last reference to the
task is dropped. The `act` should explicitly check for cancellation via `IO.checkCanceled` if it
should be terminated or otherwise react to the last reference being dropped.
-/
def chainTask (t : Task α) (f : α → EIO ε Unit) (prio := Task.Priority.default)
    (sync := false) : EIO ε Unit :=
  discard <| EIO.mapTask f t prio sync

/--
Creates a new task that waits for all the tasks in the list `tasks` to complete, and then runs the
`EIO ε` action `f` on their results. This new task has priority `prio`.

Running the resulting `BaseIO` action causes the task to be started eagerly. Unlike pure tasks
created by `Task.spawn`, tasks created by this function will run even if the last reference to the
task is dropped. The `act` should explicitly check for cancellation via `IO.checkCanceled` if it
should be terminated or otherwise react to the last reference being dropped.
-/
@[inline] def mapTasks (f : List α → EIO ε β) (tasks : List (Task α))
    (prio := Task.Priority.default) (sync := false) : BaseIO (Task (Except ε β)) :=
  BaseIO.mapTasks (fun as => f as |>.toBaseIO) tasks prio sync

end EIO

namespace IO

/--
Converts an `Except ε` action into an `IO` action.

If the `Except ε` action throws an exception, then the exception type's `ToString` instance is used
to convert it into an `IO.Error`, which is thrown. Otherwise, the value is returned.
-/
def ofExcept [ToString ε] (e : Except ε α) : IO α :=
  match e with
  | Except.ok a    => pure a
  | Except.error e => throw (IO.userError (toString e))

/--
Creates an IO action that will invoke `fn` if and when it is executed, returning the result.
-/
def lazyPure (fn : Unit → α) : IO α :=
  pure (fn ())

/--
Mutable reference cells that contain values of type `α`. These cells can read from and mutated in
the `IO` monad.
-/
abbrev Ref (α : Type) := ST.Ref IO.RealWorld α

instance : MonadLift (ST IO.RealWorld) BaseIO where
  monadLift mx := fun s =>
    match mx s with
    | .mk s a => .mk s a

/--
Creates a new mutable reference cell that contains `a`.
-/
def mkRef (a : α) : BaseIO (IO.Ref α) :=
  ST.mkRef a


/--
Monotonically increasing time since an unspecified past point in milliseconds. There is no relation
to wall clock time.
-/
@[extern "lean_io_mono_ms_now"] opaque monoMsNow : BaseIO Nat

/--
Monotonically increasing time since an unspecified past point in nanoseconds. There is no relation
to wall clock time.
-/
@[extern "lean_io_mono_nanos_now"] opaque monoNanosNow : BaseIO Nat

/--
Reads bytes from a system entropy source. It is not guaranteed to be cryptographically secure.

If `nBytes` is `0`, returns immediately with an empty buffer.
-/
@[extern "lean_io_get_random_bytes"] opaque getRandomBytes (nBytes : USize) : IO ByteArray

/--
Pauses execution for the specified number of milliseconds.
-/
opaque sleep (ms : UInt32) : BaseIO Unit :=
  -- TODO: add a proper primitive for IO.sleep
  fun s => dbgSleep ms fun _ => .mk () s

/--
Runs `act` in a separate `Task`, with priority `prio`. Because `IO` actions may throw an exception
of type `IO.Error`, the result of the task is an `Except IO.Error α`.

Running the resulting `BaseIO` action causes the task to be started eagerly. Pure accesses to the
`Task` do not influence the impure `act`. Because `IO` actions may throw an exception of type
`IO.Error`, the result of the task is an `Except IO.Error α`.

Unlike pure tasks created by `Task.spawn`, tasks created by this function will run even if the last
reference to the task is dropped. The `act` should explicitly check for cancellation via
`IO.checkCanceled` if it should be terminated or otherwise react to the last reference being
dropped.
-/
@[inline] def asTask (act : IO α) (prio := Task.Priority.default) : BaseIO (Task (Except IO.Error α)) :=
  EIO.asTask act prio

/--
Creates a new task that waits for `t` to complete and then runs the `IO` action `f` on its result.
This new task has priority `prio`.

Running the resulting `BaseIO` action causes the task to be started eagerly. Unlike pure tasks
created by `Task.spawn`, tasks created by this function will run even if the last reference to the
task is dropped. The `act` should explicitly check for cancellation via `IO.checkCanceled` if it
should be terminated or otherwise react to the last reference being dropped. Because `IO` actions
may throw an exception of type `IO.Error`, the result of the task is an `Except IO.Error α`.
-/
@[inline] def mapTask (f : α → IO β) (t : Task α) (prio := Task.Priority.default) (sync := false) :
    BaseIO (Task (Except IO.Error β)) :=
  EIO.mapTask f t prio sync

/--
Creates a new task that waits for `t` to complete, runs the `IO` action `f` on its result, and then
continues as the resulting task. This new task has priority `prio`.

Running the resulting `BaseIO` action causes this new task to be started eagerly. Unlike pure tasks
created by `Task.spawn`, tasks created by this function will run even if the last reference to the
task is dropped. The `act` should explicitly check for cancellation via `IO.checkCanceled` if it
should be terminated or otherwise react to the last reference being dropped. Because `IO` actions
may throw an exception of type `IO.Error`, the result of the task is an `Except IO.Error α`.
-/
@[inline] def bindTask (t : Task α) (f : α → IO (Task (Except IO.Error β)))
    (prio := Task.Priority.default) (sync := false) : BaseIO (Task (Except IO.Error β)) :=
  EIO.bindTask t f prio sync

/--
Creates a new task that waits for `t` to complete and then runs the `IO` action `f` on its result.
This new task has priority `prio`.

This is a version of `IO.mapTask` that ignores the result value.

Running the resulting `IO` action causes the task to be started eagerly. Unlike pure tasks created
by `Task.spawn`, tasks created by this function will run even if the last reference to the task is
dropped. The act should explicitly check for cancellation via `IO.checkCanceled` if it should be
terminated or otherwise react to the last reference being dropped.
-/
def chainTask (t : Task α) (f : α → IO Unit) (prio := Task.Priority.default)
    (sync := false) : IO Unit :=
  EIO.chainTask t f prio sync

/-- `IO` specialization of `EIO.mapTasks`. -/
@[inline] def mapTasks (f : List α → IO β) (tasks : List (Task α)) (prio := Task.Priority.default)
    (sync := false) : BaseIO (Task (Except IO.Error β)) :=
  EIO.mapTasks f tasks prio sync

/--
Checks whether the current task's cancellation flag has been set by calling `IO.cancel` or by
dropping the last reference to the task.
-/
@[extern "lean_io_check_canceled"] opaque checkCanceled : BaseIO Bool

/--
Requests cooperative cancellation of the task. The task must explicitly call `IO.checkCanceled` to
react to the cancellation.
-/
@[extern "lean_io_cancel"] opaque cancel : @& Task α → BaseIO Unit

/-- The current state of a `Task` in the Lean runtime's task manager. -/
inductive TaskState
  /--
  The `Task` is waiting to be run.

  It can be waiting for dependencies to complete or sitting in the task manager queue waiting for a
  thread to run on.
  -/
  | waiting
  /--
  The `Task` is actively running on a thread or, in the case of a `Promise`, waiting for a call to
  `IO.Promise.resolve`.
  -/
  | running
  /--
  The `Task` has finished running and its result is available. Calling `Task.get` or `IO.wait` on
  the task will not block.
  -/
  | finished
  deriving Inhabited, Repr, DecidableEq, Ord

instance : LT TaskState := ltOfOrd
instance : LE TaskState := leOfOrd
instance : Min TaskState := minOfLe
instance : Max TaskState := maxOfLe

/--
Converts a task state to a string.
-/
protected def TaskState.toString : TaskState → String
  | .waiting => "waiting"
  | .running => "running"
  | .finished => "finished"

instance : ToString TaskState := ⟨TaskState.toString⟩

/--
Returns the current state of a task in the Lean runtime's task manager.

For tasks derived from `Promise`s, the states `waiting` and `running` should be considered
equivalent.
-/
@[extern "lean_io_get_task_state"] opaque getTaskState : @& Task α → BaseIO TaskState

/--
Checks whether the task has finished execution, at which point calling `Task.get` will return
immediately.
-/
@[inline] def hasFinished (task : Task α) : BaseIO Bool := do
  return (← getTaskState task) matches .finished

/--
Waits for the task to finish, then returns its result.
-/
@[extern "lean_io_wait"] opaque wait (t : Task α) : BaseIO α :=
  return t.get

/--
Waits until any of the tasks in the list has finished, then return its result.
-/
@[extern "lean_io_wait_any"] opaque waitAny (tasks : @& List (Task α))
    (h : tasks.length > 0 := by exact Nat.zero_lt_succ _) : BaseIO α :=
  return tasks[0].get

/--
Given a non-empty list of tasks, wait for the first to complete.
Return the value and the list of remaining tasks.
-/
def waitAny' (tasks : List (Task α)) (h : 0 < tasks.length := by exact Nat.zero_lt_succ _) :
    BaseIO (α × List (Task α)) := do
  let (i, a) ← IO.waitAny
    (tasks.mapIdx fun i t => t.map (sync := true) fun a => (i, a))
    (by simp_all)
  return (a, tasks.eraseIdx i)

/--
Returns the number of _heartbeats_ that have occurred during the current thread's execution. The
heartbeat count is the number of "small" memory allocations performed in a thread.

Heartbeats used to implement timeouts that are more deterministic across different hardware.
-/
@[extern "lean_io_get_num_heartbeats"] opaque getNumHeartbeats : BaseIO Nat

/--
Sets the heartbeat counter of the current thread to the given amount. This can be used to avoid
counting heartbeats of code whose execution time is non-deterministic.
-/
@[extern "lean_io_set_heartbeats"] opaque setNumHeartbeats (count : Nat) : BaseIO Unit

/--
Adjusts the heartbeat counter of the current thread by the given amount. This can be useful to give
allocation-avoiding code additional “weight” and is also used to adjust the counter after resuming
from a snapshot.

Heartbeats are a means of implementing “deterministic” timeouts. The heartbeat counter is the number
of “small” memory allocations performed on the current execution thread.
-/
def addHeartbeats (count : Nat) : BaseIO Unit := do
  let n ← getNumHeartbeats
  setNumHeartbeats (n + count)

end IO

/--
  Marks given value and its object graph closure as multi-threaded if currently
  marked single-threaded. This will make reference counter updates atomic and
  thus more costly. It can still be useful to do eagerly when the value will be
  shared between threads later anyway and there is available time budget to mark
  it now. -/
@[extern "lean_runtime_mark_multi_threaded"]
def Runtime.markMultiThreaded (a : α) : BaseIO α := return a

/--
Marks given value and its object graph closure as persistent. This will remove
reference counter updates but prevent the closure from being deallocated until
the end of the process! It can still be useful to do eagerly when the value
will be marked persistent later anyway and there is available time budget to
mark it now or it would be unnecessarily marked multi-threaded in between.

This function is only safe to use on objects (in the full closure) which are
not used concurrently or which are already persistent.
-/
@[extern "lean_runtime_mark_persistent"]
unsafe def Runtime.markPersistent (a : α) : BaseIO α := return a

set_option linter.unusedVariables false in
/--
Discards the passed owned reference. This leads to `a` any any object reachable from it never being
freed. This can be a useful optimization for eliding deallocation time of big object graphs that are
kept alive close to the end of the process anyway (in which case calling `Runtime.markPersistent`
would be similarly costly to deallocation). It is still considered a safe operation as it cannot
lead to undefined behavior.
-/
@[extern "lean_runtime_forget"]
def Runtime.forget (a : α) : BaseIO Unit := return
