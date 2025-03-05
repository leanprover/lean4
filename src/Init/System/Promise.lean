/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
prelude
import Init.System.IO

set_option linter.missingDocs true

namespace IO

private opaque PromisePointed : NonemptyType.{0}

private structure PromiseImpl (α : Type) : Type where
  prom : PromisePointed.type
  h    : Nonempty α

/--
`Promise α` allows you to create a `Task α` whose value is provided later by calling `resolve`.

Typical usage is as follows:
1. `let promise ← Promise.new` creates a promise
2. `promise.result? : Task (Option α)` can now be passed around
3. `promise.result?.get` blocks until the promise is resolved
4. `promise.resolve a` resolves the promise
5. `promise.result?.get` now returns `some a`

If the promise is dropped without ever being resolved, `promise.result?.get` will return `none`.
See `Promise.result!/resultD` for other ways to handle this case.
-/
def Promise (α : Type) : Type := PromiseImpl α

instance [s : Nonempty α] : Nonempty (Promise α) :=
  Nonempty.intro { prom := Classical.choice PromisePointed.property, h := s }

/-- Creates a new `Promise`. -/
@[extern "lean_io_promise_new"]
opaque Promise.new [Nonempty α] : BaseIO (Promise α)

/--
Resolves a `Promise`.

Only the first call to this function has an effect.
-/
@[extern "lean_io_promise_resolve"]
opaque Promise.resolve (value : α) (promise : @& Promise α) : BaseIO Unit

/--
Like `Promise.result`, but resolves to `none` if the promise is dropped without ever being resolved.
-/
@[extern "lean_io_promise_result_opt"]
opaque Promise.result? (promise : @& Promise α) : Task (Option α)

-- SU: not planning to make this public without a lot more thought and motivation
@[extern "lean_option_get_or_block"]
private opaque Option.getOrBlock! [Nonempty α] : Option α → α

/--
The result task of a `Promise`.

The task blocks until `Promise.resolve` is called. If the promise is dropped without ever being
resolved, evaluating the task will panic and, when not using fatal panics, block forever. Use
`Promise.result?` to handle this case explicitly.
-/
def Promise.result! (promise : @& Promise α) : Task α :=
  let _ : Nonempty α := promise.h
  promise.result?.map (sync := true) Option.getOrBlock!

@[inherit_doc Promise.result!, deprecated Promise.result! (since := "2025-02-05")]
def Promise.result := @Promise.result!

/--
Like `Promise.result`, but resolves to `dflt` if the promise is dropped without ever being resolved.
-/
@[macro_inline] def Promise.resultD (promise : Promise α) (dflt : α) : Task α :=
  promise.result?.map (sync := true) (·.getD dflt)

/--
Checks whether the promise has already been resolved, i.e. whether access to `result*` will return
immediately.
-/
def Promise.isResolved (promise : Promise α) : BaseIO Bool :=
  IO.hasFinished promise.result?
