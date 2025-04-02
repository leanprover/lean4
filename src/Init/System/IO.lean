/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Jared Roesch, Leonardo de Moura, Sebastian Ullrich, Mac Malone
-/
prelude
import Init.System.IOError
import Init.System.FilePath
import Init.System.ST
import Init.Data.Ord

open System

/--
A representation of “the real world” that's used in `IO` monads to ensure that `IO` actions are not
reordered.
-/
/- Like <https://hackage.haskell.org/package/ghc-Prim-0.5.2.0/docs/GHC-Prim.html#t:RealWorld>.
   Makes sure we never reorder `IO` operations.

   TODO: mark opaque -/
def IO.RealWorld : Type := Unit

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
def EIO (ε : Type) : Type → Type := EStateM ε IO.RealWorld

instance : Monad (EIO ε) := inferInstanceAs (Monad (EStateM ε IO.RealWorld))
instance : MonadFinally (EIO ε) := inferInstanceAs (MonadFinally (EStateM ε IO.RealWorld))
instance : MonadExceptOf ε (EIO ε) := inferInstanceAs (MonadExceptOf ε (EStateM ε IO.RealWorld))
instance : OrElse (EIO ε α) := ⟨MonadExcept.orElse⟩
instance [Inhabited ε] : Inhabited (EIO ε α) := inferInstanceAs (Inhabited (EStateM ε IO.RealWorld α))

/--
An `IO` monad that cannot throw exceptions.
-/
def BaseIO := EIO Empty

instance : Monad BaseIO := inferInstanceAs (Monad (EIO Empty))
instance : MonadFinally BaseIO := inferInstanceAs (MonadFinally (EIO Empty))

/--
Runs a `BaseIO` action, which cannot throw an exception, in any other `EIO` monad.

This function is usually used implicitly via [automatic monadic
lifting](lean-manual://section/lifting-monads) rather being than called explicitly.
-/
@[always_inline, inline]
def BaseIO.toEIO (act : BaseIO α) : EIO ε α :=
  fun s => match act s with
  | EStateM.Result.ok a s => EStateM.Result.ok a s

instance : MonadLift BaseIO (EIO ε) := ⟨BaseIO.toEIO⟩

/--
Converts an `EIO ε` action that might throw an exception of type `ε` into an exception-free `BaseIO`
action that returns an `Except` value.
-/
@[always_inline, inline]
def EIO.toBaseIO (act : EIO ε α) : BaseIO (Except ε α) :=
  fun s => match act s with
  | EStateM.Result.ok a s     => EStateM.Result.ok (Except.ok a) s
  | EStateM.Result.error ex s => EStateM.Result.ok (Except.error ex) s

/--
Handles any exception that might be thrown by an `EIO ε` action, transforming it into an
exception-free `BaseIO` action.
-/
@[always_inline, inline]
def EIO.catchExceptions (act : EIO ε α) (h : ε → BaseIO α) : BaseIO α :=
  fun s => match act s with
  | EStateM.Result.ok a s     => EStateM.Result.ok a s
  | EStateM.Result.error ex s => h ex s

/--
Converts an `Except ε` action into an `EIO ε` action.

If the `Except ε` action throws an exception, then the resulting `EIO ε` action throws the same
exception. Otherwise, the value is returned.
-/
def EIO.ofExcept (e : Except ε α) : EIO ε α :=
  match e with
  | Except.ok a    => pure a
  | Except.error e => throw e

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
  act.adaptExcept f

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
  act.adaptExcept f

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
@[inline] unsafe def unsafeBaseIO (fn : BaseIO α) : α :=
  match fn.run () with
  | EStateM.Result.ok a _ => a

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
def sleep (ms : UInt32) : BaseIO Unit :=
  -- TODO: add a proper primitive for IO.sleep
  fun s => dbgSleep ms fun _ => EStateM.Result.ok () s

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
Returns the number of _heartbeats_ that have occurred during the current thread's execution. The
heartbeat count is the number of “small” memory allocations performed in a thread.

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

/--
Whether a file should be opened for reading, writing, creation and writing, or appending.

A the operating system level, this translates to the mode of a file handle (i.e., a set of `open`
flags and an `fdopen` mode).

None of the modes represented by this datatype translate line endings (i.e. `O_BINARY` on Windows).
Furthermore, they are not inherited across process creation (i.e. `O_NOINHERIT` on Windows and
`O_CLOEXEC` elsewhere).

**Operating System Specifics:**
* Windows:
  [`_open`](https://learn.microsoft.com/en-us/cpp/c-runtime-library/reference/open-wopen?view=msvc-170),
  [`_fdopen`](https://learn.microsoft.com/en-us/cpp/c-runtime-library/reference/fdopen-wfdopen?view=msvc-170)
* Linux: [`open`](https://linux.die.net/man/2/open), [`fdopen`](https://linux.die.net/man/3/fdopen)
-/
inductive FS.Mode where
  /--
  The file should be opened for reading.

  The read/write cursor is positioned at the beginning of the file. It is an error if the file does
  not exist.

  * `open` flags: `O_RDONLY`
  * `fdopen` mode: `r`
  -/
  | read
  /--
  The file should be opened for writing.

  If the file already exists, it is truncated to zero length. Otherwise, a new file is created. The
  read/write cursor is positioned at the beginning of the file.

  * `open` flags: `O_WRONLY | O_CREAT | O_TRUNC`
  * `fdopen` mode: `w`
  -/
  | write
  /--
  A new file should be created for writing.

  It is an error if the file already exists. A new file is created, with the read/write cursor
  positioned at the start.

  * `open` flags: `O_WRONLY | O_CREAT | O_TRUNC | O_EXCL`
  * `fdopen` mode: `w`
  -/
  | writeNew
  /--
  The file should be opened for both reading and writing.

  It is an error if the file does not already exist. The read/write cursor is positioned at the
  start of the file.

  * `open` flags: `O_RDWR`
  * `fdopen` mode: `r+`
  -/
  | readWrite
  /--
  The file should be opened for writing.

  If the file does not already exist, it is created. If the file already exists, it is opened, and
  the read/write cursor is positioned at the end of the file.

  * `open` flags: `O_WRONLY | O_CREAT | O_APPEND`
  * `fdopen` mode: `a`
  -/
  | append

/--
A reference to an opened file.

File handles wrap the underlying operating system's file descriptors. There is no explicit operation
to close a file: when the last reference to a file handle is dropped, the file is closed
automatically.

Handles have an associated read/write cursor that determines the where reads and writes occur in the
file.
-/
opaque FS.Handle : Type := Unit

/--
A pure-Lean abstraction of POSIX streams. These streams may represent an underlying POSIX stream or
be implemented by Lean code.

Because standard input, standard output, and standard error are all `IO.FS.Stream`s that can be
overridden, Lean code may capture and redirect input and output.
-/
structure FS.Stream where
  /--
  Flushes the stream's output buffers.
  -/
  flush   : IO Unit
  /--
  Reads up to the given number of bytes from the stream.

  If the returned array is empty, an end-of-file marker (EOF) has been reached. An EOF does not
  actually close a stream, so further reads may block and return more data.
  -/
  read    : USize → IO ByteArray
  /--
  Writes the provided bytes to the stream.

  If the stream represents a physical output device such as a file on disk, then the results may be
  buffered. Call `FS.Stream.flush` to synchronize their contents.
  -/
  write   : ByteArray → IO Unit
  /--
  Reads text up to and including the next newline from the stream.

  If the returned string is empty, an end-of-file marker (EOF) has been reached.
  An EOF does not actually close a stream, so further reads may block and return more data.
  -/
  getLine : IO String
  /--
  Writes the provided string to the stream.
  -/
  putStr  : String → IO Unit
  /-- Returns `true` if a stream refers to a Windows console or Unix terminal. -/
  isTty   : BaseIO Bool
  deriving Inhabited

open FS

/--
Returns the current thread's standard input stream.

Use `IO.setStdin` to replace the current thread's standard input stream.
-/
@[extern "lean_get_stdin"] opaque getStdin  : BaseIO FS.Stream
/--
Returns the current thread's standard output stream.

Use `IO.setStdout` to replace the current thread's standard output stream.
-/
@[extern "lean_get_stdout"] opaque getStdout : BaseIO FS.Stream
/--
Returns the current thread's standard error stream.

Use `IO.setStderr` to replace the current thread's standard error stream.
-/
@[extern "lean_get_stderr"] opaque getStderr : BaseIO FS.Stream

/--
Replaces the standard input stream of the current thread and returns its previous value.

Use `IO.getStdin` to get the current standard input stream.
-/
@[extern "lean_get_set_stdin"] opaque setStdin  : FS.Stream → BaseIO FS.Stream
/--
Replaces the standard output stream of the current thread and returns its previous value.

Use `IO.getStdout` to get the current standard output stream.
-/
@[extern "lean_get_set_stdout"] opaque setStdout : FS.Stream → BaseIO FS.Stream
/--
Replaces the standard error stream of the current thread and returns its previous value.

Use `IO.getStderr` to get the current standard error stream.
-/
@[extern "lean_get_set_stderr"] opaque setStderr : FS.Stream → BaseIO FS.Stream

/--
Iterates an `IO` action. Starting with an initial state, the action is applied repeatedly until it
returns a final value in `Sum.inr`. Each time it returns `Sum.inl`, the returned value is treated as
a new sate.
-/
@[specialize] partial def iterate (a : α) (f : α → IO (Sum α β)) : IO β := do
  let v ← f a
  match v with
  | Sum.inl a => iterate a f
  | Sum.inr b => pure b

namespace FS

namespace Handle

/--
Opens the file at `fn` with the given `mode`.

An exception is thrown if the file cannot be opened.
-/
@[extern "lean_io_prim_handle_mk"] opaque mk (fn : @& FilePath) (mode : FS.Mode) : IO Handle

/--
Acquires an exclusive or shared lock on the handle. Blocks to wait for the lock if necessary.

Acquiring a exclusive lock while already possessing a shared lock will **not** reliably succeed: it
works on Unix-like systems but not on Windows.
-/
@[extern "lean_io_prim_handle_lock"] opaque lock (h : @& Handle) (exclusive := true) : IO Unit
/--
Tries to acquire an exclusive or shared lock on the handle and returns `true` if successful. Will
not block if the lock cannot be acquired, but instead returns `false`.

Acquiring a exclusive lock while already possessing a shared lock will **not** reliably succeed: it
works on Unix-like systems but not on Windows.
-/
@[extern "lean_io_prim_handle_try_lock"] opaque tryLock (h : @& Handle) (exclusive := true) : IO Bool
/--
Releases any previously-acquired lock on the handle. Succeeds even if no lock has been acquired.
-/
@[extern "lean_io_prim_handle_unlock"] opaque unlock (h : @& Handle) : IO Unit

/--
Returns `true` if a handle refers to a Windows console or a Unix terminal.
-/
@[extern "lean_io_prim_handle_is_tty"] opaque isTty (h : @& Handle) : BaseIO Bool

/--
Flushes the output buffer associated with the handle, writing any unwritten data to the associated
output device.
-/
@[extern "lean_io_prim_handle_flush"] opaque flush (h : @& Handle) : IO Unit
/--
Rewinds the read/write cursor to the beginning of the handle's file.
-/
@[extern "lean_io_prim_handle_rewind"] opaque rewind (h : @& Handle) : IO Unit
/--
Truncates the handle to its read/write cursor.

This operation does not automatically flush output buffers, so the contents of the output device may
not reflect the change immediately. This does not usually lead to problems because the read/write
cursor includes buffered writes. However, buffered writes followed by `IO.FS.Handle.rewind`, then
`IO.FS.Handle.truncate`, and then closing the file may lead to a non-empty file. If unsure, call
`IO.FS.Handle.flush` before truncating.
-/
@[extern "lean_io_prim_handle_truncate"] opaque truncate (h : @& Handle) : IO Unit
/--
Reads up to the given number of bytes from the handle. If the returned array is empty, an
end-of-file marker (EOF) has been reached.

Encountering an EOF does not close a handle. Subsequent reads may block and return more data.
-/
@[extern "lean_io_prim_handle_read"] opaque read (h : @& Handle) (bytes : USize) : IO ByteArray
/--
Writes the provided bytes to the the handle.

Writing to a handle is typically buffered, and may not immediately modify the file on disk. Use
`IO.FS.Handle.flush` to write changes to buffers to the associated device.
-/
@[extern "lean_io_prim_handle_write"] opaque write (h : @& Handle) (buffer : @& ByteArray) : IO Unit

/--
Reads UTF-8-encoded text up to and including the next line break from the handle. If the returned
string is empty, an end-of-file marker (EOF) has been reached.

Encountering an EOF does not close a handle. Subsequent reads may block and return more data.
-/
@[extern "lean_io_prim_handle_get_line"] opaque getLine (h : @& Handle) : IO String
/--
Writes the provided string to the file handle using the UTF-8 encoding.

Writing to a handle is typically buffered, and may not immediately modify the file on disk. Use
`IO.FS.Handle.flush` to write changes to buffers to the associated device.
-/
@[extern "lean_io_prim_handle_put_str"] opaque putStr (h : @& Handle) (s : @& String) : IO Unit

end Handle

/--
Resolves a path to an absolute path that contains no '.', '..', or symbolic links.

This function coincides with the [POSIX `realpath`
function](https://pubs.opengroup.org/onlinepubs/9699919799/functions/realpath.html).
-/
@[extern "lean_io_realpath"] opaque realPath (fname : FilePath) : IO FilePath

/--
Removes (deletes) a file from the filesystem.

To remove a directory, use `IO.FS.removeDir` or `IO.FS.removeDirAll` instead.
-/
@[extern "lean_io_remove_file"] opaque removeFile (fname : @& FilePath) : IO Unit

/--
Removes (deletes) a directory.

Removing a directory fails if the directory is not empty. Use `IO.FS.removeDirAll` to remove
directories along with their contents.
-/
@[extern "lean_io_remove_dir"] opaque removeDir : @& FilePath → IO Unit
/--
Creates a directory at the specified path. The parent directory must already exist.

Throws an exception if the directory cannot be created.
-/
@[extern "lean_io_create_dir"] opaque createDir : @& FilePath → IO Unit


/--
Moves a file or directory `old` to the new location `new`.

This function coincides with the [POSIX `rename`
function](https://pubs.opengroup.org/onlinepubs/9699919799/functions/rename.html).
-/
@[extern "lean_io_rename"] opaque rename (old new : @& FilePath) : IO Unit

/--
Creates a temporary file in the most secure manner possible, returning both a `Handle` to the
already-opened file and its path.

There are no race conditions in the file’s creation. The file is readable and writable only by the
creating user ID. Additionally on UNIX style platforms the file is executable by nobody.

It is the caller's job to remove the file after use. Use `withTempFile` to ensure that the temporary
file is removed.
-/
@[extern "lean_io_create_tempfile"] opaque createTempFile : IO (Handle × FilePath)

/--
Creates a temporary directory in the most secure manner possible, returning the new directory's
path. There are no race conditions in the directory’s creation. The directory is readable and
writable only by the creating user ID.

It is the caller's job to remove the directory after use. Use `withTempDir` to ensure that the
temporary directory is removed.
-/
@[extern "lean_io_create_tempdir"] opaque createTempDir : IO FilePath

end FS

/--
Returns the value of the environment variable `var`, or `none` if it is not present in the
environment.
-/
@[extern "lean_io_getenv"] opaque getEnv (var : @& String) : BaseIO (Option String)
/--
Returns the file name of the currently-running executable.
-/
@[extern "lean_io_app_path"] opaque appPath : IO FilePath
/--
Returns the current working directory of the executing process.
-/
@[extern "lean_io_current_dir"] opaque currentDir : IO FilePath

namespace FS

/--
Opens the file `fn` with the specified `mode` and passes the resulting file handle to `f`.

The file handle is closed when the last reference to it is dropped. If references escape `f`, then
the file remains open even after `IO.FS.withFile` has finished.
-/
@[inline]
def withFile (fn : FilePath) (mode : Mode) (f : Handle → IO α) : IO α :=
  Handle.mk fn mode >>= f

/--
Writes the contents of the string to the handle, followed by a newline. Uses UTF-8.
-/
def Handle.putStrLn (h : Handle) (s : String) : IO Unit :=
  h.putStr (s.push '\n')

/--
Reads the entire remaining contents of the file handle until an end-of-file marker (EOF) is
encountered.

The underlying file is not automatically closed upon encountering an EOF, and subsequent reads from
the handle may block and/or return data.
-/
partial def Handle.readBinToEndInto (h : Handle) (buf : ByteArray) : IO ByteArray := do
  let rec loop (acc : ByteArray) : IO ByteArray := do
    let buf ← h.read 1024
    if buf.isEmpty then
      return acc
    else
      loop (acc ++ buf)
  loop buf

/--
Reads the entire remaining contents of the file handle until an end-of-file marker (EOF) is
encountered.

The underlying file is not automatically closed upon encountering an EOF, and subsequent reads from
the handle may block and/or return data.
-/
partial def Handle.readBinToEnd (h : Handle) : IO ByteArray := do
  h.readBinToEndInto .empty

/--
Reads the entire remaining contents of the file handle as a UTF-8-encoded string. An exception is
thrown if the contents are not valid UTF-8.

The underlying file is not automatically closed, and subsequent reads from the handle may block
and/or return data.
-/
def Handle.readToEnd (h : Handle) : IO String := do
  let data ← h.readBinToEnd
  match String.fromUTF8? data with
  | some s => return s
  | none => throw <| .userError s!"Tried to read from handle containing non UTF-8 data."

/--
Returns the contents of a UTF-8-encoded text file as an array of lines.

Newline markers are not included in the lines.
-/
partial def lines (fname : FilePath) : IO (Array String) := do
  let h ← Handle.mk fname Mode.read
  let rec read (lines : Array String) := do
    let line ← h.getLine
    if line.length == 0 then
      pure lines
    else if line.back == '\n' then
      let line := line.dropRight 1
      let line := if line.back == '\r' then line.dropRight 1 else line
      read <| lines.push line
    else
      pure <| lines.push line
  read #[]

/--
Write the provided bytes to a binary file at the specified path.
-/
def writeBinFile (fname : FilePath) (content : ByteArray) : IO Unit := do
  let h ← Handle.mk fname Mode.write
  h.write content

/--
Write contents of a string to a file at the specified path using UTF-8 encoding.
-/
def writeFile (fname : FilePath) (content : String) : IO Unit := do
  let h ← Handle.mk fname Mode.write
  h.putStr content


/--
Writes the contents of the string to the stream, followed by a newline.
-/
def Stream.putStrLn (strm : FS.Stream) (s : String) : IO Unit :=
  strm.putStr (s.push '\n')

/-- An entry in a directory on a filesystem. -/
structure DirEntry where
  /-- The directory in which the entry is found. -/
  root     : FilePath
  /-- The name of the entry. -/
  fileName : String
  deriving Repr

/-- The path of the file indicated by the directory entry. -/
def DirEntry.path (entry : DirEntry) : FilePath :=
  entry.root / entry.fileName

/-- Types of files that may be found on a filesystem. -/
inductive FileType where
  /-- Directories don't have contents, but may contain other files. -/
  | dir
  /-- Ordinary files that have contents and are not directories. -/
  | file
  /-- Symbolic links that are pointers to other named files. -/
  | symlink
  /-- Files that are neither ordinary files, directories, or symbolic links. -/
  | other
  deriving Repr, BEq

/--
Low-level system time, tracked in whole seconds and additional nanoseconds.
-/
structure SystemTime where
  /-- The number of whole seconds. -/
  sec  : Int
  /-- The number of additional nanoseconds. -/
  nsec : UInt32
  deriving Repr, BEq, Ord, Inhabited

instance : LT SystemTime := ltOfOrd
instance : LE SystemTime := leOfOrd

/--
File metadata.

The metadata for a file can be accessed with `System.FilePath.metadata`.
-/
structure Metadata where
  --permissions : ...
  /-- File access time. -/
  accessed : SystemTime
  /-- File modification time. -/
  modified : SystemTime
  /-- The size of the file in bytes. -/
  byteSize : UInt64
  /--
  Whether the file is an ordinary file, a directory, a symbolic link, or some other kind of file.
  -/
  type     : FileType
  deriving Repr

end FS
end IO

namespace System.FilePath
open IO

/--
Returns the contents of the indicated directory. Throws an exception if the file does not exist or
is not a directory.
-/
@[extern "lean_io_read_dir"]
opaque readDir : @& FilePath → IO (Array IO.FS.DirEntry)

/--
Returns metadata for the indicated file. Throws an exception if the file does not exist or the
metadata cannot be accessed.
-/
@[extern "lean_io_metadata"]
opaque metadata : @& FilePath → IO IO.FS.Metadata

/--
Checks whether the indicated path can be read and is a directory.
-/
def isDir (p : FilePath) : BaseIO Bool := do
  match (← p.metadata.toBaseIO) with
  | Except.ok m => return m.type == IO.FS.FileType.dir
  | Except.error _ => return false

/--
Checks whether the indicated path points to a file that exists.
-/
def pathExists (p : FilePath) : BaseIO Bool :=
  return (← p.metadata.toBaseIO).toBool

/--
Traverses a filesystem starting at the path `p` and exploring directories that satisfy `enter`,
returning the paths visited.

The traversal is a preorder traversal, in which parent directories occur prior to any of their
children. Symbolic links are followed.
-/
partial def walkDir (p : FilePath) (enter : FilePath → IO Bool := fun _ => pure true) : IO (Array FilePath) :=
  Prod.snd <$> StateT.run (go p) #[]
where
  go p := do
    if !(← enter p) then
      return ()
    for d in (← p.readDir) do
      modify (·.push d.path)
      match (← d.path.metadata.toBaseIO) with
      | .ok { type := .symlink, .. } =>
        let p' ← FS.realPath d.path
        if (← p'.isDir) then
          -- do not call `enter` on a non-directory symlink
          if (← enter p) then
            go p'
      | .ok { type := .dir, .. } => go d.path
      | .ok _ => pure ()
      -- entry vanished, ignore
      | .error (.noFileOrDirectory ..) => pure ()
      | .error e => throw e

end System.FilePath

namespace IO

namespace FS

/--
Reads the entire contents of the binary file at the given path as an array of bytes.
-/
def readBinFile (fname : FilePath) : IO ByteArray := do
  -- Requires metadata so defined after metadata
  let mdata ← fname.metadata
  let size := mdata.byteSize.toUSize
  let handle ← IO.FS.Handle.mk fname .read
  let buf ←
    if size > 0 then
      handle.read mdata.byteSize.toUSize
    else
      pure <| ByteArray.emptyWithCapacity 0
  handle.readBinToEndInto buf

/--
Reads the entire contents of the UTF-8-encoded file at the given path as a `String`.

An exception is thrown if the contents of the file are not valid UTF-8. This is in addition to
exceptions that may always be thrown as a result of failing to read files.
-/
def readFile (fname : FilePath) : IO String := do
  let data ← readBinFile fname
  match String.fromUTF8? data with
  | some s => return s
  | none => throw <| .userError s!"Tried to read file '{fname}' containing non UTF-8 data."

end FS

/--
Runs an action with the specified stream `h` as standard input, restoring the original standard
input stream afterwards.
-/
def withStdin [Monad m] [MonadFinally m] [MonadLiftT BaseIO m] (h : FS.Stream) (x : m α) : m α := do
  let prev ← setStdin h
  try x finally discard <| setStdin prev

/--
Runs an action with the specified stream `h` as standard output, restoring the original standard
output stream afterwards.
-/
def withStdout [Monad m] [MonadFinally m] [MonadLiftT BaseIO m] (h : FS.Stream) (x : m α) : m α := do
  let prev ← setStdout h
  try
    x
  finally
    discard <| setStdout prev

/--
Runs an action with the specified stream `h` as standard error, restoring the original standard
error stream afterwards.
-/
def withStderr [Monad m] [MonadFinally m] [MonadLiftT BaseIO m] (h : FS.Stream) (x : m α) : m α := do
  let prev ← setStderr h
  try x finally discard <| setStderr prev

/--
Converts `s` to a string using its `ToString α` instance, and prints it to the current standard
output (as determined by `IO.getStdout`).
-/
def print [ToString α] (s : α) : IO Unit := do
  let out ← getStdout
  out.putStr <| toString s

/--
Converts `s` to a string using its `ToString α` instance, and prints it with a trailing newline to
the current standard output (as determined by `IO.getStdout`).
-/
def println [ToString α] (s : α) : IO Unit :=
  print ((toString s).push '\n')

/--
Converts `s` to a string using its `ToString α` instance, and prints it to the current standard
error (as determined by `IO.getStderr`).
-/
def eprint [ToString α] (s : α) : IO Unit := do
  let out ← getStderr
  out.putStr <| toString s

/--
Converts `s` to a string using its `ToString α` instance, and prints it with a trailing newline to
the current standard error (as determined by `IO.getStderr`).
-/
def eprintln [ToString α] (s : α) : IO Unit :=
  eprint <| toString s |>.push '\n'

@[export lean_io_eprint]
private def eprintAux (s : String) : IO Unit :=
  eprint s

@[export lean_io_eprintln]
private def eprintlnAux (s : String) : IO Unit :=
  eprintln s

/--
Returns the directory that the current executable is located in.
-/
def appDir : IO FilePath := do
  let p ← appPath
  let some p ← pure p.parent
    | throw <| IO.userError s!"IO.appDir: unexpected filename '{p}'"
  FS.realPath p

namespace FS

/--
Creates a directory at the specified path, creating all missing parents as directories.
-/
partial def createDirAll (p : FilePath) : IO Unit := do
  if ← p.isDir then
    return ()
  if let some parent := p.parent then
    createDirAll parent
  try
    createDir p
  catch
    | e =>
      if ← p.isDir then
        pure ()  -- I guess someone else was faster
      else
        throw e

/--
  Fully remove given directory by deleting all contained files and directories in an unspecified order.
  Fails if any contained entry cannot be deleted or was newly created during execution. -/
partial def removeDirAll (p : FilePath) : IO Unit := do
  for ent in (← p.readDir) do
    if (← ent.path.isDir : Bool) then
      removeDirAll ent.path
    else
      removeFile ent.path
  removeDir p

/--
Creates a temporary file in the most secure manner possible and calls `f` with both a `Handle` to
the already-opened file and its path. Afterwards, the temporary file is deleted.

There are no race conditions in the file’s creation. The file is readable and writable only by the
creating user ID. Additionally on UNIX style platforms the file is executable by nobody.

Use `IO.FS.createTempFile` to avoid the automatic deletion of the temporary file.
-/
def withTempFile [Monad m] [MonadFinally m] [MonadLiftT IO m] (f : Handle → FilePath → m α) :
    m α := do
  let (handle, path) ← createTempFile
  try
    f handle path
  finally
    removeFile path

/--
Creates a temporary directory in the most secure manner possible, providing a its path to an `IO`
action. Afterwards, all files in the temporary directory are recursively deleted, regardless of how
or when they were created.

There are no race conditions in the directory’s creation. The directory is readable and writable
only by the creating user ID. Use `IO.FS.createTempDir` to avoid the automatic deletion of the
directory's contents.
-/
def withTempDir [Monad m] [MonadFinally m] [MonadLiftT IO m] (f : FilePath → m α) :
    m α := do
  let path ← createTempDir
  try
    f path
  finally
    removeDirAll path

end FS

namespace Process

/-- Returns the current working directory of the calling process. -/
@[extern "lean_io_process_get_current_dir"] opaque getCurrentDir : IO FilePath

/-- Sets the current working directory of the calling process. -/
@[extern "lean_io_process_set_current_dir"] opaque setCurrentDir (path : @& FilePath) : IO Unit

/-- Returns the process ID of the calling process. -/
@[extern "lean_io_process_get_pid"] opaque getPID : BaseIO UInt32

/--
Whether the standard input, output, and error handles of a child process should be attached to
pipes, inherited from the parent, or null.

If the stream is a pipe, then the parent process can use it to communicate with the child.
-/
inductive Stdio where
  /-- The stream should be attached to a pipe. -/
  | piped
  /-- The stream should be inherited from the parent process. -/
  | inherit
  /-- The stream should be empty. -/
  | null

/--
The type of handles that can be used to communicate with a child process on its standard input,
output, or error streams.

For `IO.Process.Stdio.piped`, this type is `IO.FS.Handle`. Otherwise, it is `Unit`, because no
communication is possible.
-/
def Stdio.toHandleType : Stdio → Type
  | Stdio.piped   => FS.Handle
  | Stdio.inherit => Unit
  | Stdio.null    => Unit

/--
Configuration for the standard input, output, and error handles of a child process.
-/
structure StdioConfig where
  /-- Configuration for the process' stdin handle. -/
  stdin := Stdio.inherit
  /-- Configuration for the process' stdout handle. -/
  stdout := Stdio.inherit
  /-- Configuration for the process' stderr handle. -/
  stderr := Stdio.inherit

/--
Configuration for a child process to be spawned.

Use `IO.Process.spawn` to start the child process. `IO.Process.output` and `IO.Process.run` can be
used when the child process should be run to completion, with its output and/or error code captured.
-/
structure SpawnArgs extends StdioConfig where
  /-- Command name. -/
  cmd : String
  /-- Arguments for the command. -/
  args : Array String := #[]
  /-- The child process's working directory. Inherited from the parent current process if `none`. -/
  cwd : Option FilePath := none
  /--
  Add or remove environment variables for the child process.

  The child process inherits the parent's environment, as modified by `env`. Keys in the array are
  the names of environment variables. A `none`, causes the entry to be removed from the environment,
  and `some` sets the variable to the new value, adding it if necessary. Variables are processed from left to right.
  -/
  env : Array (String × Option String) := #[]
  /--
  Starts the child process in a new session and process group using `setsid`. Currently a no-op on
  non-POSIX platforms.
  -/
  setsid : Bool := false

/--
A child process that was spawned with configuration `cfg`.

The configuration determines whether the child process's standard input, standard output, and
standard error are `IO.FS.Handle`s or `Unit`.
-/
structure Child (cfg : StdioConfig) where private mk ::
  /--
  The child process's standard input handle, if it was configured as `IO.Process.Stdio.piped`, or
  `()` otherwise.
  -/
  stdin  : cfg.stdin.toHandleType
  /--
  The child process's standard output handle, if it was configured as `IO.Process.Stdio.piped`, or
  `()` otherwise.
  -/
  stdout : cfg.stdout.toHandleType
  /--
  The child process's standard error handle, if it was configured as `IO.Process.Stdio.piped`, or
  `()` otherwise.
  -/
  stderr : cfg.stderr.toHandleType

/--
Starts a child process with the provided configuration. The child process is spawned using operating
system primitives, and it can be written in any language.

The child process runs in parallel with the parent.

If the child process's standard input is a pipe, use `IO.Process.Child.takeStdin` to make it
possible to close the child's standard input before the process terminates, which provides the child with an end-of-file marker.
-/
@[extern "lean_io_process_spawn"] opaque spawn (args : SpawnArgs) : IO (Child args.toStdioConfig)

/--
Blocks until the child process has exited and return its exit code.
-/
@[extern "lean_io_process_child_wait"] opaque Child.wait {cfg : @& StdioConfig} : @& Child cfg → IO UInt32

/--
Checks whether the child has exited. Returns `none` if the process has not exited, or its exit code
if it has.
-/
@[extern "lean_io_process_child_try_wait"] opaque Child.tryWait {cfg : @& StdioConfig} : @& Child cfg →
    IO (Option UInt32)

/--
Terminates the child process using the `SIGTERM` signal or a platform analogue.

If the process was started using `SpawnArgs.setsid`, terminates the entire process group instead.
-/
@[extern "lean_io_process_child_kill"] opaque Child.kill {cfg : @& StdioConfig} : @& Child cfg → IO Unit

/--
Extracts the `stdin` field from a `Child` object, allowing the handle to be closed while maintaining
a reference to the child process.

File handles are closed when the last reference to them is dropped. Closing the child's standard
input causes an end-of-file marker. Because the `Child` object has a reference to the standard
input, this operation is necessary in order to close the stream while the process is running (e.g.
to extract its exit code after calling `Child.wait`). Many processes do not terminate until their
standard input is exhausted.
-/
@[extern "lean_io_process_child_take_stdin"] opaque Child.takeStdin {cfg : @& StdioConfig} : Child cfg →
    IO (cfg.stdin.toHandleType × Child { cfg with stdin := Stdio.null })

/-- Returns the operating system process id of the child process. -/
@[extern "lean_io_process_child_pid"] opaque Child.pid {cfg : @& StdioConfig} : Child cfg → UInt32

/--
The result of running a process to completion.
-/
structure Output where
  /-- The process's exit code. -/
  exitCode : UInt32
  /-- Everything that was written to the process's standard output. -/
  stdout   : String
  /-- Everything that was written to the process's standard error. -/
  stderr   : String

/--
Runs a process to completion and captures its output and exit code. The child process is run with a
null standard input, and the current process blocks until it has run to completion.

The specifications of standard input, output, and error handles in `args` are ignored.
-/
def output (args : SpawnArgs) : IO Output := do
  let child ← spawn { args with stdout := .piped, stderr := .piped, stdin := .null }
  let stdout ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let stderr ← child.stderr.readToEnd
  let exitCode ← child.wait
  let stdout ← IO.ofExcept stdout.get
  pure { exitCode := exitCode, stdout := stdout, stderr := stderr }

/--
Runs a process to completion, blocking until it terminates. If the child process terminates
successfully with exit code 0, its standard output is returned. An exception is thrown if it
terminates with any other exit code.
-/
def run (args : SpawnArgs) : IO String := do
  let out ← output args
  if out.exitCode != 0 then
    throw <| IO.userError <| "process '" ++ args.cmd ++ "' exited with code " ++ toString out.exitCode
  pure out.stdout

/--
Terminates the current process with the provided exit code. `0` indicates success, all other values
indicate failure.
-/
@[extern "lean_io_exit"] opaque exit : UInt8 → IO α

end Process

/-- Returns the thread ID of the calling thread. -/
@[extern "lean_io_get_tid"] opaque getTID : BaseIO UInt64

/--
POSIX-style file permissions.

The `FileRight` structure describes these permissions for a file's owner, members of it's designated
group, and all others.
-/
structure AccessRight where
  /-- The file can be read. -/
  read : Bool := false
  /-- The file can be written to. -/
  write : Bool := false
  /-- The file can be executed. -/
  execution : Bool := false

/--
Converts individual POSIX-style file permissions to their conventional three-bit representation.

This is the bitwise `or` of the following:
 * If the file can be read, `0x4`, otherwise `0`.
 * If the file can be written, `0x2`, otherwise `0`.
 * If the file can be executed, `0x1`, otherwise `0`.

Examples:
 * `{read := true : AccessRight}.flags = 4`
 * `{read := true, write := true : AccessRight}.flags = 6`
 * `{read := true, execution := true : AccessRight}.flags = 5`
-/
def AccessRight.flags (acc : AccessRight) : UInt32 :=
  let r : UInt32 := if acc.read      then 0x4 else 0
  let w : UInt32 := if acc.write     then 0x2 else 0
  let x : UInt32 := if acc.execution then 0x1 else 0
  r.lor <| w.lor x

/--
POSIX-style file permissions that describe access rights for a file's owner, members of its
assigned group, and all others.
-/
structure FileRight where
  /-- The owner's permissions to access the file. -/
  user  : AccessRight := {}
  /-- The assigned group's permissions to access the file. -/
  group : AccessRight := {}
  /-- The permissions that all others have to access the file. -/
  other : AccessRight := {}

/--
Converts POSIX-style file permissions to their numeric representation, with three bits each for the
owner's permissions, the group's permissions, and others' permissions.
-/
def FileRight.flags (acc : FileRight) : UInt32 :=
  let u : UInt32 := acc.user.flags.shiftLeft 6
  let g : UInt32 := acc.group.flags.shiftLeft 3
  let o : UInt32 := acc.other.flags
  u.lor <| g.lor o

@[extern "lean_chmod"] opaque Prim.setAccessRights (filename : @& FilePath) (mode : UInt32) : IO Unit

/--
Sets the POSIX-style permissions for a file.
-/
def setAccessRights (filename : FilePath) (mode : FileRight) : IO Unit :=
  Prim.setAccessRights filename mode.flags

/--
Mutable reference cells that contain values of type `α`. These cells can read from and mutated in
the `IO` monad.
-/
abbrev Ref (α : Type) := ST.Ref IO.RealWorld α

instance : MonadLift (ST IO.RealWorld) BaseIO := ⟨id⟩

/--
Creates a new mutable reference cell that contains `a`.
-/
def mkRef (a : α) : BaseIO (IO.Ref α) :=
  ST.mkRef a

/--
Mutable cell that can be passed around for purposes of cooperative task cancellation: request
cancellation with `CancelToken.set` and check for it with `CancelToken.isSet`.

This is a more flexible alternative to `Task.cancel` as the token can be shared between multiple
tasks.
-/
structure CancelToken where
  private ref : IO.Ref Bool
deriving Nonempty

namespace CancelToken

/-- Creates a new cancellation token. -/
def new : BaseIO CancelToken :=
  CancelToken.mk <$> IO.mkRef false

/-- Activates a cancellation token. Idempotent. -/
def set (tk : CancelToken) : BaseIO Unit :=
  tk.ref.set true

/-- Checks whether the cancellation token has been activated. -/
def isSet (tk : CancelToken) : BaseIO Bool :=
  tk.ref.get

-- separate definition as otherwise no unboxed version is generated
@[export lean_io_cancel_token_is_set]
private def isSetExport := @isSet

end CancelToken

namespace FS
namespace Stream

/--
Creates a Lean stream from a file handle. Each stream operation is implemented by the corresponding
file handle operation.
-/
@[export lean_stream_of_handle]
def ofHandle (h : Handle) : Stream where
  flush   := Handle.flush h
  read    := Handle.read h
  write   := Handle.write h
  getLine := Handle.getLine h
  putStr  := Handle.putStr h
  isTty   := Handle.isTty h

/--
A byte buffer that can simulate a file in memory.

Use `IO.FS.Stream.ofBuffer` to create a stream from a buffer.
-/
structure Buffer where
  /-- The contents of the buffer. -/
  data : ByteArray := ByteArray.empty
  /-- The read/write cursor's position in the buffer. -/
  pos  : Nat := 0

/--
Creates a stream from a mutable reference to a buffer.

The resulting stream simulates a file, mutating the contents of the reference in response to writes
and reading from it in response to reads. These streams can be used with `IO.withStdin`,
`IO.setStdin`, and the corresponding operators for standard output and standard error to redirect
input and output.
-/
def ofBuffer (r : Ref Buffer) : Stream where
  flush   := pure ()
  read    := fun n => r.modifyGet fun b =>
    let data := b.data.extract b.pos (b.pos + n.toNat)
    (data, { b with pos := b.pos + data.size })
  write   := fun data => r.modify fun b =>
    -- set `exact` to `false` so that repeatedly writing to the stream does not impose quadratic run time
    { b with data := data.copySlice 0 b.data b.pos data.size false, pos := b.pos + data.size }
  getLine := do
    let buf ← r.modifyGet fun b =>
      let pos := match b.data.findIdx? (start := b.pos) fun u => u == 0 || u = '\n'.toNat.toUInt8 with
        -- include '\n', but not '\0'
        | some pos => if b.data.get! pos == 0 then pos else pos + 1
        | none     => b.data.size
      (b.data.extract b.pos pos, { b with pos := pos })
    match String.fromUTF8? buf with
    | some str => pure str
    | none => throw (.userError "invalid UTF-8")
  putStr  := fun s => r.modify fun b =>
    let data := s.toUTF8
    { b with data := data.copySlice 0 b.data b.pos data.size false, pos := b.pos + data.size }
  isTty   := pure false

end Stream

/--
Runs an action with `stdin` emptied and `stdout` and `stderr` captured into a `String`. If
`isolateStderr` is `false`, only `stdout` is captured.
-/
def withIsolatedStreams [Monad m] [MonadFinally m] [MonadLiftT BaseIO m] (x : m α)
    (isolateStderr := true) : m (String × α) := do
  let bIn ← mkRef { : Stream.Buffer }
  let bOut ← mkRef { : Stream.Buffer }
  let r ← withStdin (Stream.ofBuffer bIn) <|
    withStdout (Stream.ofBuffer bOut) <|
      (if isolateStderr then withStderr (Stream.ofBuffer bOut) else id) <|
        x
  let bOut ← liftM (m := BaseIO) bOut.get
  let out := String.fromUTF8! bOut.data
  pure (out, r)

end FS
end IO

syntax "println! " (interpolatedStr(term) <|> term) : term

macro_rules
  | `(println! $msg:interpolatedStr) => `((IO.println (s! $msg) : IO Unit))
  | `(println! $msg:term)            => `((IO.println $msg : IO Unit))

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
