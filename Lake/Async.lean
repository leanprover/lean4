/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/

namespace Lake

-- # Async / Await

class Async (m : Type u → Type v) (n : outParam $ Type u → Type u) where
  async : m α → m (n α)

export Async (async)

class Await (m : Type u → Type v) (n : outParam $ Type u → Type u) where
  await : n α → m α

export Await (await)

class MonadAsync (m : Type u → Type v) (n : outParam $ Type u → Type u) [Monad m] extends Async m n, Await m n where
  mapAsync  {α β : Type u} : (α → m β) → n α → m (n β)     := fun f x => async (await x >>= f)
  bindAsync {α β : Type u} : n α → (α → m (n β)) → m (n β) := fun x f => async (await x >>= f >>= await)

export MonadAsync (mapAsync bindAsync)

section
variable [Monad m] [MonadAsync m n]

-- ## List Utilities

/-- `MonadAsync` version of `IO.mapTasks` -/
def mapListAsync (f : List α → m β) (ts : List (n α)) : m (n β) :=
  go ts []
where
  go
    | [], as => async (f as.reverse)
    | t::ts, as => bindAsync t fun a => go ts (a :: as)

def afterListAsync (task : m (n β)) : (ts : List (n α)) → m (n β)
  | [] => task
  | t::ts => bindAsync t fun _ => afterListAsync task ts

def andThenListAsync (task : (n α)) : (ts : List (n α)) → m (n α)
  | [] => task
  | t::ts => bindAsync task fun _ => andThenListAsync t ts

def seqListAsync [Pure n] : (ts : List (n PUnit)) → m (n PUnit)
  | [] => pure (pure ())
  | t::ts => andThenListAsync t ts

-- ## Array Utilities
-- These Follow the pattern of Array iterators established in the Lean core.

@[inline] unsafe def mapArrayAsyncUnsafe (f : Array α → m β) (ts : Array (n α)) (start := 0) (stop := ts.size) : m (n β) :=
 let rec @[specialize] fold (i : USize) (stop : USize) (as : Array α) : m (n β) := do
    if i == stop then
      async (f as)
    else
      bindAsync (ts.uget i lcProof) fun a => fold (i+1) stop (as.push a)
  if start < stop then
    if stop ≤ ts.size then
      fold (USize.ofNat start) (USize.ofNat stop) (Array.mkEmpty (start - stop))
    else
      async (f #[])
  else
    async (f #[])

@[implementedBy mapArrayAsyncUnsafe]
def mapArrayAsync (f : Array α → m β) (ts : Array (n α)) (start := 0) (stop := ts.size) : m (n β) :=
  let fold (stop : Nat) (h : stop ≤ ts.size) :=
    let rec loop (i : Nat) (j : Nat) (as : Array α) : m (n β) := do
      if hlt : j < stop then
        match i with
        | Nat.zero => async (f as)
        | Nat.succ i' =>
          let t := ts.get ⟨j, Nat.ltOfLtOfLe hlt h⟩
          bindAsync t fun a => loop i' (j+1) (as.push a)
      else
        async (f as)
    loop (stop - start) start (Array.mkEmpty (stop - start))
  if h : stop ≤ ts.size then
    fold stop h
  else
    fold ts.size (Nat.leRefl _)

@[inline] unsafe def afterArrayAsyncUnsafe (task : m (n β)) (ts : Array (n α)) (start := 0) (stop := ts.size) : m (n β) :=
 let rec @[specialize] fold (i : USize) (stop : USize) : m (n β) := do
    if i == stop then
      task
    else
      bindAsync (ts.uget i lcProof) fun _ => fold (i+1) stop
  if start < stop then
    if stop ≤ ts.size then
      fold (USize.ofNat start) (USize.ofNat stop)
    else
      task
  else
    task

@[implementedBy afterArrayAsyncUnsafe]
def afterArrayAsync (task : m (n β)) (ts : Array (n α)) (start := 0) (stop := ts.size) : m (n β) :=
  let fold (stop : Nat) (h : stop ≤ ts.size) :=
    let rec loop (i : Nat) (j : Nat) : m (n β) := do
      if hlt : j < stop then
        match i with
        | Nat.zero => task
        | Nat.succ i' =>
          let t := ts.get ⟨j, Nat.ltOfLtOfLe hlt h⟩
          bindAsync t fun a => loop i' (j+1)
      else
        task
    loop (stop - start) start
  if h : stop ≤ ts.size then
    fold stop h
  else
    fold ts.size (Nat.leRefl _)

def seqArrayAsync [Pure n] (ts : Array (n PUnit)) : m (n PUnit) :=
  if h : 0 < ts.size then
    afterArrayAsync (ts.get ⟨ts.size - 1, Nat.subLt h (by decide)⟩) ts.pop
  else
    pure (pure ())

end
