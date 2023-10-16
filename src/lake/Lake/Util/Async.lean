/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.Task
import Lake.Util.OptionIO
import Lake.Util.Lift

/-!
This module Defines the asynchronous monadic interface for Lake.
The interface is composed of three major abstract monadic types:

* `m`: The monad of the synchronous action (e.g., `IO`).
* `n`: The monad of the (a)synchronous task manager (e.g., `BaseIO`).
* `k`: The monad of the (a)synchronous task (e.g., `IOTask`).

The definitions within this module provide the basic utilities for converting
between these monads and combining them in different ways.
-/

namespace Lake

--------------------------------------------------------------------------------
/-! # Async / Await Abstraction -/
--------------------------------------------------------------------------------

class Sync (m : Type u → Type v) (n : outParam $ Type u' → Type w) (k : outParam $ Type u → Type u') where
  /-- Run the monadic action as a synchronous task. -/
  sync : m α → n (k α)

export Sync (sync)

class Async (m : Type u → Type v) (n : outParam $ Type u' → Type w) (k : outParam $ Type u → Type u') where
  /-- Run the monadic action as an asynchronous task. -/
  async : m α → n (k α)

export Async (async)

class Await (k : Type u → Type v) (m : outParam $ Type u → Type w)  where
  /-- Wait for an (a)synchronous task to finish. -/
  await : k α → m α

export Await (await)

/-! ## Standard Instances -/

instance : Sync Id Id Task := ⟨Task.pure⟩
instance : Sync BaseIO BaseIO BaseIOTask := ⟨Functor.map Task.pure⟩

instance [Sync m n k] : Sync (ReaderT ρ m) (ReaderT ρ n) k where
  sync x := fun r => sync (x r)

instance [Sync m n k] : Sync (ExceptT ε m) n (ExceptT ε k) where
  sync x := cast (by delta ExceptT; rfl) <| sync (n := n) x.run

instance [Sync m n k] : Sync (OptionT m) n (OptionT k) where
  sync x := cast (by delta OptionT; rfl) <| sync (n := n) x.run

instance : Sync (EIO ε) BaseIO (EIOTask ε) where
  sync x := sync <| ExceptT.mk x.toBaseIO

instance : Sync OptionIO BaseIO OptionIOTask where
  sync x := sync <| OptionT.mk x.toBaseIO

instance : Async Id Id Task := ⟨Task.pure⟩
instance : Async BaseIO BaseIO BaseIOTask := ⟨BaseIO.asTask⟩

instance [Async m n k] : Async (ReaderT ρ m) (ReaderT ρ n) k where
  async x := fun r => async (x r)

instance [Async m n k] : Async (ExceptT ε m) n (ExceptT ε k) where
  async x := cast (by delta ExceptT; rfl) <| async (n := n) x.run

instance [Async m n k] : Async (OptionT m) n (OptionT k) where
  async x := cast (by delta OptionT; rfl) <| async (n := n) x.run

instance : Async (EIO ε) BaseIO (EIOTask ε) where
  async x := async <| ExceptT.mk x.toBaseIO

instance : Async OptionIO BaseIO OptionIOTask where
  async x := async <| OptionT.mk x.toBaseIO

instance : Await Task Id := ⟨Task.get⟩

instance : Await (EIOTask ε) (EIO ε) where
  await x := IO.wait x >>= liftM

instance : Await OptionIOTask OptionIO where
  await x := IO.wait x >>= liftM

instance [Await k m] : Await (ExceptT ε k) (ExceptT ε m) where
  await x := ExceptT.mk <| await x.run

instance [Await k m] : Await (OptionT k) (OptionT m) where
  await x := OptionT.mk <| await x.run

--------------------------------------------------------------------------------
/-! # Combinators -/
--------------------------------------------------------------------------------

class BindSync (m : Type u → Type v) (n : outParam $ Type u' → Type w) (k : outParam $ Type u → Type u') where
  /-- Perform a synchronous action after another (a)synchronous task completes successfully. -/
  bindSync {α β : Type u} : Task.Priority → k α → (α → m β) → n (k β)

export BindSync (bindSync)

class BindAsync (n : Type u → Type v) (k : Type u → Type u) where
  /-- Perform a asynchronous task after another (a)synchronous task completes successfully. -/
  bindAsync {α β : Type u} : k α → (α → n (k β)) → n (k β)

export BindAsync (bindAsync)

class SeqAsync (n : outParam $ Type u → Type v) (k : Type u → Type u) where
  /-- Combine two (a)synchronous tasks, applying the result of the second one to the first one. -/
  seqAsync {α β : Type u} : k (α → β) → k α → n (k β)

export SeqAsync (seqAsync)

class SeqLeftAsync (n : outParam $ Type u → Type v) (k : Type u → Type u) where
  /-- Combine two (a)synchronous tasks, returning the result of the first one. -/
  seqLeftAsync {α β : Type u} : k α → k β → n (k α)

export SeqLeftAsync (seqLeftAsync)

class SeqRightAsync (n : outParam $ Type u → Type v) (k : Type u → Type u) where
  /-- Combine two (a)synchronous tasks, returning the result of the second one. -/
  seqRightAsync {α β : Type u} : k α → k β → n (k β)

export SeqRightAsync (seqRightAsync)

class SeqWithAsync (n : outParam $ Type u → Type v) (k : Type u → Type u) where
  /-- Combine two (a)synchronous tasks using `f`. -/
  seqWithAsync {α β : Type u} : (f : α → β → γ) → k α → k β → n (k γ)

export SeqWithAsync (seqWithAsync)

class ApplicativeAsync (n : outParam $ Type u → Type v) (k : Type u → Type u)
extends SeqAsync n k, SeqLeftAsync n k, SeqRightAsync n k, SeqWithAsync n k where
  seqAsync      := seqWithAsync fun f a => f a
  seqLeftAsync  := seqWithAsync fun a _ => a
  seqRightAsync := seqWithAsync fun _ b => b

/-! ## Standard Instances -/

instance : BindSync Id Id Task := ⟨fun _ => flip Task.map⟩
instance : BindSync BaseIO BaseIO BaseIOTask := ⟨fun _ => flip BaseIO.mapTask⟩

instance : BindSync (EIO ε) BaseIO (ETask ε) where
  bindSync prio ka f := ka.run |> BaseIO.mapTask (prio := prio) fun
    | Except.ok a => f a |>.toBaseIO
    | Except.error e => pure <| Except.error e

instance : BindSync OptionIO BaseIO OptionIOTask where
  bindSync prio ka f := ka.run |> BaseIO.mapTask (prio := prio) fun
    | some a => f a |>.toBaseIO
    | none => pure none

instance [BindSync m n k] : BindSync (ReaderT ρ m) (ReaderT ρ n) k where
  bindSync prio ka f := fun r => bindSync prio ka fun a => f a r

instance [BindSync m n k] [Pure m] : BindSync (ExceptT ε m) n (ExceptT ε k) where
  bindSync prio ka f := cast (by delta ExceptT; rfl) <| bindSync prio (n := n) ka.run fun
    | Except.ok a => f a |>.run
    | Except.error e => pure <| Except.error e

instance [BindSync m n k] [Pure m] : BindSync (OptionT m) n (OptionT k) where
  bindSync prio ka f := cast (by delta OptionT; rfl) <| bindSync prio ka.run fun
    | some a => f a |>.run
    | none => pure none

instance : BindAsync Id Task := ⟨Task.bind⟩
instance : BindAsync BaseIO BaseIOTask := ⟨BaseIO.bindTask⟩

instance : BindAsync BaseIO (EIOTask ε) where
  bindAsync ka f := BaseIO.bindTask ka.run fun
    | Except.ok a => f a
    | Except.error e => pure <| pure (Except.error e)

instance : BindAsync BaseIO OptionIOTask where
  bindAsync ka f := BaseIO.bindTask ka.run fun
    | some a => f a
    | none => pure (pure none)

instance [BindAsync n k] : BindAsync (ReaderT ρ n) k where
  bindAsync ka f := fun r => bindAsync ka fun a => f a r

instance [BindAsync n k] [Pure n] [Pure k] : BindAsync n (ExceptT ε k) where
  bindAsync ka f := cast (by delta ExceptT; rfl) <| bindAsync ka.run fun
    | Except.ok a => f a
    | Except.error e => pure <| pure <| Except.error e

instance [BindAsync n k] [Pure n] [Pure k] : BindAsync n (OptionT k) where
  bindAsync ka f := cast (by delta OptionT; rfl) <| bindAsync ka.run fun
    | some a => f a
    | none => pure (pure none)

instance : ApplicativeAsync Id Task where
  seqWithAsync f ka kb := ka.bind fun a => kb.bind fun b => pure <| f a b

instance : ApplicativeAsync BaseIO BaseIOTask where
  seqWithAsync f ka kb := BaseIO.bindTask ka fun a => BaseIO.bindTask kb fun b => pure <| pure <| f a b

instance [ApplicativeAsync n k] : ApplicativeAsync n (ExceptT ε k) where
  seqWithAsync f ka kb :=
    let h xa xb : Except ε _ := return f (← xa) (← xb)
    cast (by delta ExceptT; rfl) <| seqWithAsync (n := n) h ka kb

instance [ApplicativeAsync n k] : ApplicativeAsync n (OptionT k) where
  seqWithAsync f ka kb :=
    let h xa xb : Option _ := return f (← xa) (← xb)
    cast (by delta OptionT; rfl) <| seqWithAsync (n := n) h ka kb

--------------------------------------------------------------------------------
/-! #  List/Array Utilities -/
--------------------------------------------------------------------------------

/-! ## Sequencing (A)synchronous Tasks -/

/-- Combine all (a)synchronous tasks in a `List` from right to left into a single task ending `last`. -/
def seqLeftList1Async [SeqLeftAsync n k] [Monad n] (last : (k α)) : (tasks : List (k α)) → n (k α)
| [] => return last
| t::ts => seqLeftList1Async t ts >>= (seqLeftAsync last ·)

/-- Combine all (a)synchronous tasks in a `List` from right to left into a single task. -/
def seqLeftListAsync [SeqLeftAsync n k] [Monad n] [Pure k] : (tasks : List (k PUnit)) → n (k PUnit)
| [] => return (pure ())
| t::ts => seqLeftList1Async t ts

/-- Combine all (a)synchronous tasks in a `List` from left to right into a single task. -/
def seqRightListAsync [SeqRightAsync n k] [Monad n] [Pure k] : (tasks : List (k PUnit)) → n (k PUnit)
| [] => return (pure ())
| t::ts => ts.foldlM seqRightAsync t

/-- Combine all (a)synchronous tasks in a `Array` from right to left into a single task. -/
def seqLeftArrayAsync [SeqLeftAsync n k] [Monad n] [Pure k] (tasks : Array (k PUnit)) : n (k PUnit) :=
  if h : 0 < tasks.size then
    tasks.pop.foldrM seqLeftAsync (tasks.get ⟨tasks.size - 1, Nat.sub_lt h (by decide)⟩)
  else
    return (pure ())

/-- Combine all (a)synchronous tasks in a `Array` from left to right into a single task. -/
def seqRightArrayAsync [SeqRightAsync n k] [Monad n] [Pure k] (tasks : Array (k PUnit)) : n (k PUnit) :=
  if h : 0 < tasks.size then
    tasks.foldlM seqRightAsync (tasks.get ⟨0, h⟩)
  else
    return (pure ())

/-! ## Folding (A)synchronous Tasks -/

variable [SeqWithAsync n k] [Monad n] [Pure k]

/-- Fold a `List` of (a)synchronous tasks from right to left (i.e., a right fold) into a single task. -/
def foldLeftListAsync (f : α → β → β) (init : β) (tasks : List (k α)) : n (k β) :=
  tasks.foldrM (seqWithAsync f) (pure init)

/-- Fold an `Array` of (a)synchronous tasks from right to left (i.e., a right fold) into a single task. -/
def foldLeftArrayAsync (f : α → β → β) (init : β) (tasks : Array (k α)) : n (k β) :=
  tasks.foldrM (seqWithAsync f) (pure init)

/-- Fold a `List` of (a)synchronous tasks from left to right (i.e., a left fold) into a single task. -/
def foldRightListAsync (f : β → α → β) (init : β) (tasks : List (k α)) : n (k β) :=
  tasks.foldlM (seqWithAsync f) (pure init)

/-- Fold an `Array` of (a)synchronous tasks from left to right (i.e., a left fold) into a single task. -/
def foldRightArrayAsync (f : β → α → β) (init : β) (tasks : Array (k α)) : n (k β) :=
  tasks.foldlM (seqWithAsync f) (pure init)
