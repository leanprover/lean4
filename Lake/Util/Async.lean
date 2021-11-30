/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.Task
import Lake.Util.OptionIO

namespace Lake

def liftOption [Alternative m] : Option α → m α
| some a => pure a
| none => failure

instance [MonadLift m n] : MonadLift (ReaderT ρ m) (ReaderT ρ n) where
  monadLift x := fun r => liftM <| x r

--------------------------------------------------------------------------------
-- # Async / Await Abstraction
--------------------------------------------------------------------------------

class Async (m : Type u → Type v) (n : outParam $ Type u' → Type w) (k : outParam $ Type u → Type u') where
  /- Run the monadic action as an asynchronous task. -/
  async : m α → n (k α)

export Async (async)

class Await (k : Type u → Type v) (m : outParam $ Type u → Type w)  where
  /- Wait for an asynchronous task to finish. -/
  await : k α → m α

export Await (await)

-- ## Instances

instance : Async Id Id Task := ⟨Task.pure⟩
instance : Async (Unit → ·) Id Task := ⟨Task.spawn⟩
instance : Async BaseIO BaseIO BaseIOTask := ⟨BaseIO.asTask⟩
instance : Async (EIO ε) BaseIO (EIOTask ε) := ⟨EIO.asTask⟩
instance : Async OptionIO BaseIO OptionIOTask := ⟨OptionIO.asTask⟩

instance [Async m n k] : Async (ReaderT ρ m) (ReaderT ρ n) k where
  async x := fun r => async (x r)

instance [Async m n k] : Async (ExceptT ε m) n (ExceptT ε k) where
  async x := cast (by simp [ExceptT]) <| async (n := n) x.run

instance [Async m n k] : Async (OptionT m) n (OptionT k) where
  async x := cast (by simp [OptionT]) <| async (n := n) x.run

instance : Await Task Id := ⟨Task.get⟩

instance : Await (EIOTask ε) (EIO ε) where
  await x := IO.wait x >>= liftExcept

instance : Await OptionIOTask OptionIO where
  await x := IO.wait x >>= liftOption

instance [Await k m] : Await (ExceptT ε k) (ExceptT ε m) where
  await x := ExceptT.mk <| await x.run

instance [Await k m] : Await (OptionT k) (OptionT m) where
  await x := OptionT.mk <| await x.run

--------------------------------------------------------------------------------
-- # Combinators
--------------------------------------------------------------------------------

class BindAsync (n : Type u → Type v) (k :  outParam $ Type u → Type u) where
  /-- Perform a asynchronous task after another asynchronous task completes successfully. -/
  bindAsync {α β : Type u} : k α → (α → n (k β)) → n (k β)

export BindAsync (bindAsync)

class BindAsync' (m : Type u → Type v) (n : outParam $ Type u' → Type w) (k : outParam $ Type u → Type u') where
  /-- Perform a synchronous action after another asynchronous task completes successfully. -/
  bindAsync' {α β : Type u} : k α → (α → m β) → n (k β)

export BindAsync' (bindAsync')

class SeqMapAsync (n : outParam $ Type u → Type v) (k : Type u → Type u) where
  /-- Combine two asynchronous tasks using `f`. -/
  seqMapAsync {α β : Type u} : (f : α → β → γ) → k α → k β → n (k γ)

export SeqMapAsync (seqMapAsync)

class SeqLeftAsync (n : outParam $ Type u → Type v) (k : Type u → Type u) where
  /-- Combine two asynchronous tasks, returning the result of the first one. -/
  seqLeftAsync {α β : Type u} : k α → k β → n (k α)

export SeqLeftAsync (seqLeftAsync)

class SeqRightAsync (n : outParam $ Type u → Type v) (k : Type u → Type u) where
  /-- Combine two asynchronous tasks, returning the result of the second one. -/
  seqRightAsync {α β : Type u} : k α → k β → n (k β)

export SeqRightAsync (seqRightAsync)

-- ## Instances

instance : BindAsync Id Task := ⟨Task.bind⟩
instance : BindAsync BaseIO BaseIOTask := ⟨BaseIO.bindTask⟩

instance : BindAsync BaseIO (EIOTask ε) where
  bindAsync ka f := BaseIO.bindTask ka.run fun
    | Except.ok a => f a
    | Except.error e => pure <| pure (Except.error e)

instance : BindAsync BaseIO OptionIOTask where
  bindAsync ka f := BaseIO.bindTask ka.run fun
    | some a => f a
    | none => pure <| pure none

instance [BindAsync n k] : BindAsync (ReaderT ρ n) k where
  bindAsync ka f := fun r => bindAsync ka fun a => f a r

instance [BindAsync n k] [Pure n] [Pure k] : BindAsync n (ExceptT ε k) where
  bindAsync ka f := cast (by simp [ExceptT]) <| bindAsync ka.run fun
    | Except.ok a => f a
    | Except.error e => pure <| pure <| Except.error e

instance [BindAsync n k] [Pure n] [Pure k] : BindAsync n (OptionT k) where
  bindAsync ka f := cast (by simp [OptionT]) <| bindAsync ka.run fun
    | some a => f a
    | none => pure <| pure <| none

instance : BindAsync' Id Id Task := ⟨flip Task.map⟩
instance : BindAsync' BaseIO BaseIO BaseIOTask := ⟨flip BaseIO.mapTask⟩

instance : BindAsync' (EIO ε) BaseIO (ETask ε) where
  bindAsync' ka f := ka.run |> BaseIO.mapTask fun
    | Except.ok a => f a |>.toBaseIO
    | Except.error e => pure <| Except.error e

instance : BindAsync' OptionIO BaseIO OptionIOTask where
  bindAsync' ka f := ka.run |> BaseIO.mapTask fun
    | some a => f a |>.toBaseIO
    | none => pure none

instance [BindAsync' m n k] : BindAsync' (ReaderT ρ m) (ReaderT ρ n) k where
  bindAsync' ka f := fun r => bindAsync' ka fun a => f a r

instance [BindAsync' m n k] [Pure m] : BindAsync' (ExceptT ε m) n (ExceptT ε k) where
  bindAsync' ka f := cast (by simp [ExceptT]) <| bindAsync' (n := n) ka.run fun
    | Except.ok a => f a |>.run
    | Except.error e => pure <| Except.error e

instance [BindAsync' m n k] [Pure m] : BindAsync' (OptionT m) n (OptionT k) where
  bindAsync' ka f := cast (by simp [OptionT]) <| bindAsync' ka.run fun
    | some a => f a |>.run
    | none => pure none

instance : SeqMapAsync Id Task where
  seqMapAsync f ka kb := ka.bind fun a => kb >>= fun b => pure <| f a b

instance : SeqMapAsync BaseIO BaseIOTask where
  seqMapAsync f ka kb := BaseIO.bindTask ka fun a => BaseIO.bindTask kb fun b => pure <| f a b

instance [SeqMapAsync n k] : SeqMapAsync n (ExceptT ε k) where
  seqMapAsync f ka kb :=
    let h xa xb : Except ε _ := Id.run <| ExceptT.run do
      let a ← liftExcept xa
      let b ← liftExcept xb
      pure <| f a b
    cast (by simp [ExceptT]) <| seqMapAsync (n := n) h ka kb

instance [SeqMapAsync n k] : SeqMapAsync n (OptionT k) where
  seqMapAsync f ka kb :=
    let h xa xb := Id.run <| OptionT.run do
      let a ← liftOption xa
      let b ← liftOption xb
      pure <| f a b
    cast (by simp [OptionT]) <| seqMapAsync (n := n) h ka kb

instance [SeqMapAsync n k] : SeqLeftAsync n k where
  seqLeftAsync ka kb := seqMapAsync (fun a _ => a) ka kb

instance [SeqMapAsync n k] : SeqRightAsync n k where
  seqRightAsync ka kb := seqMapAsync (fun _ b => b) ka kb

--------------------------------------------------------------------------------
-- #  List/Array Utilities
--------------------------------------------------------------------------------

-- ## Sequencing Asynchronous Tasks

/-- Combine all asynchronous tasks in a `List` from right to left into a single task ending `last`. -/
def seqLeftList1Async [SeqLeftAsync n k] [Monad n] (last : (k α)) : (tasks : List (k α)) → n (k α)
  | [] => pure last
  | t::ts => seqLeftList1Async t ts >>= (seqLeftAsync last ·)

/-- Combine all asynchronous tasks in a `List` from right to left into a single task. -/
def seqLeftListAsync [SeqLeftAsync n k] [Monad n] [Pure k] : (tasks : List (k PUnit)) → n (k PUnit)
  | [] => pure (pure ())
  | t::ts => seqLeftList1Async t ts

/-- Combine all asynchronous tasks in a `List` from left to right into a single task. -/
def seqRightListAsync [SeqRightAsync n k] [Monad n] [Pure k] : (tasks : List (k PUnit)) → n (k PUnit)
  | [] => pure (pure ())
  | t::ts => ts.foldlM seqRightAsync t

/-- Combine all asynchronous tasks in a `Array` from right to left into a single task. -/
def seqLeftArrayAsync [SeqLeftAsync n k] [Monad n] [Pure k] (tasks : Array (k PUnit)) : n (k PUnit) :=
  if h : 0 < tasks.size then
    tasks.pop.foldrM seqLeftAsync (tasks.get ⟨tasks.size - 1, Nat.sub_lt h (by decide)⟩)
  else
    pure (pure ())

/-- Combine all asynchronous tasks in a `Array` from left to right into a single task. -/
def seqRightArrayAsync [SeqRightAsync n k] [Monad n] [Pure k] (tasks : Array (k PUnit)) : n (k PUnit) :=
  if h : 0 < tasks.size then
    tasks.foldlM seqRightAsync (tasks.get ⟨0, h⟩)
  else
    pure (pure ())

-- ## Folding Asynchronous Tasks

/-- Fold asynchronous tasks in a `List` from right to left (i.e., a right fold) into a single task. -/
def foldLeftListAsync [SeqMapAsync n k] [Monad n] [Pure k]
(f : α → β → β) (init : β) (tasks : List (k α)) : n (k β) :=
  tasks.foldrM (seqMapAsync f) init

/-- Fold asynchronous tasks in a `Array` from right to left (i.e., a right fold) into a single task. -/
def foldLeftArrayAsync [SeqMapAsync n k] [Monad n] [Pure k]
(f : α → β → β) (init : β) (tasks : Array (k α)) : n (k β) :=
  tasks.foldrM (seqMapAsync f) init

/-- Fold asynchronous tasks in a `List` from left to right (i.e., a left fold) into a single task. -/
def foldRightListAsync [SeqMapAsync n k] [Monad n] [Pure k]
(f : β → α → β) (init : β) (tasks : List (k α)) : n (k β) :=
  tasks.foldlM (seqMapAsync f) init

/-- Fold asynchronous tasks in a `Array` from left to right (i.e., a left fold) into a single task. -/
def foldRightArrayAsync [SeqMapAsync n k] [Monad n] [Pure k]
(f : β → α → β) (init : β) (tasks : Array (k α)) : n (k β) :=
  tasks.foldlM (seqMapAsync f) init
