/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Async

namespace Lake

-- # Tasks

instance : Monad Task where
  map := Task.map
  pure := Task.pure
  bind := Task.bind

abbrev ETask ε α := ExceptT ε Task α

-- # IO Tasks

def IOTask α := ETask IO.Error α
instance : Monad IOTask := inferInstanceAs <| Monad (ETask IO.Error)

namespace IOTask

def spawn (act : IO α) (prio := Task.Priority.dedicated) : IO (IOTask α) :=
  IO.asTask act prio

def await (self : IOTask α) : IO α := do
  IO.ofExcept (← IO.wait self)

def mapAsync (f : α → IO β) (self : IOTask α) (prio := Task.Priority.dedicated) : IO (IOTask β) :=
  IO.mapTask (fun x => do let x ← IO.ofExcept x; f x) self prio

def seqLeftAsync (self : IOTask α) (act : IO β) (prio := Task.Priority.dedicated) : IO (IOTask α) :=
  IO.mapTask (fun x => IO.ofExcept x <* act) self prio

def seqRightAsync (self : IOTask α) (act : IO β) (prio := Task.Priority.dedicated) : IO (IOTask β) :=
  IO.mapTask (fun x => IO.ofExcept x *> act) self prio

instance : HAndThen (IOTask α) (IO β) (IO (IOTask β)) := ⟨seqRightAsync⟩

def bindAsync (self : IOTask α) (f : α → IO (IOTask β)) (prio := Task.Priority.dedicated) : IO (IOTask β) :=
  IO.bindTask self (fun x => do let x ← IO.ofExcept x; f x)  prio

instance : MonadAsync IO IOTask where
  async := IOTask.spawn
  await := IOTask.await
  mapAsync := IOTask.mapAsync
  bindAsync := IOTask.bindAsync
  seqLeftAsync := IOTask.seqLeftAsync
  seqRightAsync := IOTask.seqRightAsync

end IOTask

section
variable [Monad m] [MonadAsync m n]

def afterTaskList (tasks : List (n α)) (act : m β) : m (n β) :=
  afterListAsync (async act) tasks

def afterTaskArray (tasks : Array (n α)) (act : m β) : m (n β) :=
  afterArrayAsync (async act) tasks

end

instance : HAndThen (List (IOTask α)) (IO β) (IO (IOTask β)) := ⟨afterTaskList⟩
instance : HAndThen (Array (IOTask α)) (IO β) (IO (IOTask β)) := ⟨afterTaskArray⟩
