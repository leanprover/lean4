/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
prelude
import Init.System.IO

namespace IO

/-- Internally, a `Promise` is just a `Task` that is in the "Promised" or "Finished" state. -/
private opaque PromiseImpl (α : Type) : { P : Type // Nonempty α ↔ Nonempty P } :=
  ⟨Task α, fun ⟨_⟩ => ⟨⟨‹_›⟩⟩, fun ⟨⟨_⟩⟩ => ⟨‹_›⟩⟩

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
def Promise (α : Type) : Type := (PromiseImpl α).1

instance [Nonempty α] : Nonempty (Promise α) :=
  (PromiseImpl α).2.1 inferInstance

/-- Creates a new `Promise`. -/
@[extern "lean_io_promise_new"]
opaque Promise.new [Nonempty α] : BaseIO (Promise α)

/--
Resolves a `Promise`.

Only the first call to this function has an effect.
-/
@[extern "lean_io_promise_resolve"]
opaque Promise.resolve (value : α) (promise : @& Promise α) : BaseIO Unit

private unsafe def Promise.resultImpl (promise : Promise α) : Task α :=
  unsafeCast promise

/--
The result task of a `Promise`.

The task blocks until `Promise.resolve` is called.
-/
@[implemented_by Promise.resultImpl]
opaque Promise.result (promise : Promise α) : Task α :=
  have : Nonempty α := (PromiseImpl α).2.2 ⟨promise⟩
  Classical.choice inferInstance
