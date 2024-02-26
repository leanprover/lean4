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
2. `promise.result : Task α` can now be passed around
3. `promise.result.get` blocks until the promise is resolved
4. `promise.resolve a` resolves the promise
5. `promise.result.get` now returns `a`

Every promise must eventually be resolved.
Otherwise the memory used for the promise will be leaked,
and any tasks depending on the promise's result will wait forever.
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
The result task of a `Promise`.

The task blocks until `Promise.resolve` is called.
-/
@[extern "lean_io_promise_result"]
opaque Promise.result (promise : Promise α) : Task α :=
  have : Nonempty α := promise.h
  Classical.choice inferInstance
