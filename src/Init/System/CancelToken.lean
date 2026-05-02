/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

prelude
public import Init.System.Promise

public section

set_option linter.missingDocs true

namespace IO

/--
Cancellation token for cooperative task cancellation: request cancellation with
`CancelToken.set` and check for it with `CancelToken.isSet`.

This is a more flexible alternative to `Task.cancel` as the token can be shared between multiple
tasks. The underlying `Promise` allows waiting for cancellation via `CancelToken.task` without
polling.
-/
structure CancelToken where
  private promise : IO.Promise Unit
  /-- Plain `Bool` flag set in lockstep with `promise`; read by the cheap `isSet` fast path
      (e.g. on the hot `Core.checkInterrupted` C++ path) without walking the promise. -/
  private setRef : IO.Ref Bool
deriving Nonempty

namespace CancelToken

/--
Creates a new cancellation token.

Note: cannot be called from `initialize` blocks because the underlying task manager is not yet
running at that point. Construct lazily on first use instead.
-/
def new : BaseIO CancelToken := do
  let promise ← IO.Promise.new
  let setRef ← IO.mkRef false
  return { promise, setRef }

/-- Activates a cancellation token. Idempotent. -/
def set (tk : CancelToken) : BaseIO Unit := do
  tk.setRef.set true
  tk.promise.resolve ()

/-- Checks whether the cancellation token has been activated. -/
def isSet (tk : CancelToken) : BaseIO Bool :=
  tk.setRef.get

/--
A task that completes when the cancellation token is set or dropped. Useful for waiting on
cancellation without polling — e.g. as one of the tasks given to `IO.waitAny`.

Returns the underlying promise's `result?` task directly, so the same task object is returned
on every call and can safely have further dependencies attached (`Task.map`, `BaseIO.bindTask`).
The `Option` distinguishes a normal `set` (`some ()`) from the token being dropped without ever
being set (`none`). For attaching a callback, prefer `onSet`.
-/
def task (tk : CancelToken) : Task (Option Unit) :=
  tk.promise.result?

/--
Registers a callback to run when the cancellation token is set. The callback runs as a
synchronous task dependency, so it executes inline on the thread that calls `set`. If the
token is already set when `onSet` is called, the callback runs immediately.
-/
def onSet (tk : CancelToken) (action : BaseIO Unit) : BaseIO Unit :=
  BaseIO.chainTask tk.promise.result? (sync := true) fun _ => action

-- separate definition as otherwise no unboxed version is generated
@[export lean_io_cancel_token_is_set]
private def isSetExport := @isSet

end CancelToken
