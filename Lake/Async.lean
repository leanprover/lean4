/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/

namespace Lake

--------------------------------------------------------------------------------
-- # Async / Await Abstraction
--------------------------------------------------------------------------------

class Async (m : Type u → Type v) (n : outParam $ Type u → Type u) where
  /- Run the monadic action as an asynchronous task. -/
  async : m α → m (n α)

export Async (async)

class Await (n : Type u → Type u) (m : Type u → Type v)  where
  /- Wait for an asynchronous task to finish. -/
  await : n α → m α

export Await (await)

-- ## Monadic Specializations

class MapAsync (m : Type u → Type v) (n : Type u → Type u) where
  mapAsync {α β : Type u} : (α → m β) → n α → m (n β)
    -- := fun f x => async (await x >>= f)

export MapAsync (mapAsync)

class SeqLeftAsync (m : Type u → Type v) (n : Type u → Type u)  where
  seqLeftAsync {α β : Type u} : n α → m β → m (n α)
    -- := fun x y => async (await x <* y)

export SeqLeftAsync (seqLeftAsync)

class SeqRightAsync (m : Type u → Type v) (n : Type u → Type u) where
  seqRightAsync {α β : Type u} : n α → m β → m (n β)
    -- := fun x y => async (await x *> y)

export SeqRightAsync (seqRightAsync)

class BindAsync (m : Type u → Type v) (n : outParam $ Type u → Type u) where
  bindAsync {α β : Type u} : n α → (α → m (n β)) → m (n β)
    -- := fun x f => async (await x >>= f >>= await)

export BindAsync (bindAsync)

--------------------------------------------------------------------------------
-- # ReaderT Instances
--------------------------------------------------------------------------------

instance [Async m n] : Async (ReaderT ρ m) n where
  async x := fun r => async (x r)

instance [Await n m] : Await n (ReaderT ρ m) where
  await x := fun _ => await x

instance [MapAsync m n] : MapAsync (ReaderT ρ m) n where
  mapAsync f x := fun r => mapAsync (fun a => f a r) x

instance [BindAsync m n] : BindAsync (ReaderT ρ m) n where
  bindAsync x f := fun r => bindAsync x (fun a => f a r)

instance [SeqLeftAsync m n] : SeqLeftAsync (ReaderT ρ m) n where
  seqLeftAsync nx mx := fun r => seqLeftAsync nx (mx r)

instance [SeqRightAsync m n] : SeqRightAsync (ReaderT ρ m) n where
  seqRightAsync nx mx := fun r => seqRightAsync nx (mx r)

--------------------------------------------------------------------------------
-- #  List/Array Utilities
--------------------------------------------------------------------------------

def andThenAsync [Pure m] [BindAsync m n] (ta : n α) (tb : n β) : m (n β) :=
  bindAsync ta fun _ => pure tb

-- ## Sequencing Lists/Arrays of Asynchronous Tasks

section
variable [BindAsync m n]

-- ### List

/-- Spawn the asynchronous task `last` after `tasks` finish. -/
def afterListAsync (last : m (n β)) : (tasks : List (n α)) → m (n β)
  | [] => last
  | t::ts => bindAsync t fun _ => afterListAsync last ts

/-- Join all asynchronous tasks in a List into a single task beginning with `init`. -/
def joinTaskList1 [Pure m] (init : (n α)) : (tasks : List (n α)) → m (n α)
  | [] => pure init
  | t::ts => bindAsync init fun _ => joinTaskList1 t ts

/-- Join all asynchronous tasks in a List into a single task. -/
def joinTaskList [Pure m] [Pure n] : (tasks : List (n PUnit)) → m (n PUnit)
  | [] => pure (pure ())
  | t::ts => joinTaskList1 t ts

/-- Asynchronously after completing `tasks`, perform `act`. -/
def afterTaskList  [Async m n] (tasks : List (n α)) (act : m β) : m (n β) :=
  afterListAsync (async act) tasks

-- ### Array

/-- Efficient implementation of `afterArrayAsync`. Assumes Arrays are at max `USize`. -/
@[inline] unsafe def afterArrayAsyncUnsafe (last : m (n β)) (tasks : Array (n α)) (start := 0) (stop := tasks.size) : m (n β) :=
 let rec @[specialize] fold (i : USize) (stop : USize) : m (n β) :=
    if i == stop then
      last
    else
      bindAsync (tasks.uget i lcProof) fun _ => fold (i+1) stop
  if start < stop then
    if stop ≤ tasks.size then
      fold (USize.ofNat start) (USize.ofNat stop)
    else
      last
  else
    last

/-- Spawn the asynchronous task `last` after `tasks` finish. -/
@[implementedBy afterArrayAsyncUnsafe]
def afterArrayAsync (last : m (n β)) (tasks : Array (n α)) (start := 0) (stop := tasks.size) : m (n β) :=
  let fold (stop : Nat) (h : stop ≤ tasks.size) :=
    let rec loop (i : Nat) (j : Nat) : m (n β) :=
      if hlt : j < stop then
        match i with
        | Nat.zero => last
        | Nat.succ i' =>
          let t := tasks.get ⟨j, Nat.lt_of_lt_of_le hlt h⟩
          bindAsync t fun _ => loop i' (j+1)
      else
        last
    loop (stop - start) start
  if h : stop ≤ tasks.size then
    fold stop h
  else
    fold tasks.size (Nat.le_refl _)

/-- Join all asynchronous tasks in a Array into a single task. -/
def joinTaskArray [Pure m] [Pure n] (tasks : Array (n PUnit)) : m (n PUnit) :=
  if h : 0 < tasks.size then
    afterArrayAsync (tasks.get ⟨tasks.size - 1, Nat.sub_lt h (by decide)⟩) tasks.pop
  else
    pure (pure ())

/-- Asynchronously after completing `tasks`, perform `act`. -/
def afterTaskArray [Async m n] (tasks : Array (n α)) (act : m β) : m (n β) :=
  afterArrayAsync (async act) tasks

end

-- ## Folding / Mapping Lists/Arrays of Asynchronous Tasks

section
variable [BindAsync m n]

-- ### List

def foldlListAsync [Monad m] [Pure n] (f : α → β → m β) (init : β) (tasks : List (n α)) : m (n β) :=
  go tasks init
where
  go
    | [], b => pure (pure b)
    | t::tasks, b => bindAsync t fun a => f a b >>= go tasks

/-- Abstract version of `IO.mapTasks`. -/
def mapListAsync [Async m n] (f : List α → m β) (tasks : List (n α)) : m (n β) :=
  go tasks []
where
  go
    | [], as => async (f as.reverse)
    | t::tasks, as => bindAsync t fun a => go tasks (a :: as)

-- ### Array

/-- Efficient implementation of `foldlArrayAsync`. Assumes Arrays are at max `USize`. -/
@[inline] unsafe def foldlArrayAsyncUnsafe [Monad m] [Pure n]
(f : β → α → m β) (init : β) (tasks : Array (n α)) (start := 0) (stop := tasks.size) : m (n β) :=
 let rec @[specialize] fold (i : USize) (stop : USize) (b : β) : m (n β) :=
    if i == stop then
      pure (pure init)
    else
      bindAsync (tasks.uget i lcProof) fun a => f b a >>= fold (i+1) stop
  if start < stop then
    if stop ≤ tasks.size then
      fold (USize.ofNat start) (USize.ofNat stop) init
    else
      pure (pure init)
  else
    pure (pure init)

@[implementedBy foldlArrayAsyncUnsafe]
def foldlArrayAsync [Monad m] [Pure n]
(f : β → α → m β) (init : β) (tasks : Array (n α)) (start := 0) (stop := tasks.size) : m (n β) :=
  let fold (stop : Nat) (h : stop ≤ tasks.size) :=
    let rec loop (i : Nat) (j : Nat) (b : β) : m (n β) :=
      if hlt : j < stop then
        match i with
        | Nat.zero => pure (pure init)
        | Nat.succ i' =>
          let t := tasks.get ⟨j, Nat.lt_of_lt_of_le hlt h⟩
          bindAsync t fun a => f b a >>= loop i' (j+1)
      else
        pure (pure init)
    loop (stop - start) start init
  if h : stop ≤ tasks.size then
    fold stop h
  else
    fold tasks.size (Nat.le_refl _)

/-- Efficient implementation of `mapArrayAsync`. Assumes Arrays are at max `USize`. -/
@[inline] unsafe def mapArrayAsyncUnsafe [Async m n]
(f : Array α → m β) (tasks : Array (n α)) (start := 0) (stop := tasks.size) : m (n β) :=
 let rec @[specialize] fold (i : USize) (stop : USize) (as : Array α) : m (n β) :=
    if i == stop then
      async (f as)
    else
      bindAsync (tasks.uget i lcProof) fun a => fold (i+1) stop (as.push a)
  if start < stop then
    if stop ≤ tasks.size then
      fold (USize.ofNat start) (USize.ofNat stop) (Array.mkEmpty (start - stop))
    else
      async (f #[])
  else
    async (f #[])

/-- Abstract version of `IO.mapTasks` for Arrays. -/
@[implementedBy mapArrayAsyncUnsafe]
def mapArrayAsync [Async m n]
(f : Array α → m β) (tasks : Array (n α)) (start := 0) (stop := tasks.size) : m (n β) :=
  let fold (stop : Nat) (h : stop ≤ tasks.size) :=
    let rec loop (i : Nat) (j : Nat) (as : Array α) : m (n β) :=
      if hlt : j < stop then
        match i with
        | Nat.zero => async (f as)
        | Nat.succ i' =>
          let t := tasks.get ⟨j, Nat.lt_of_lt_of_le hlt h⟩
          bindAsync t fun a => loop i' (j+1) (as.push a)
      else
        async (f as)
    loop (stop - start) start (Array.mkEmpty (stop - start))
  if h : stop ≤ tasks.size then
    fold stop h
  else
    fold tasks.size (Nat.le_refl _)

end
