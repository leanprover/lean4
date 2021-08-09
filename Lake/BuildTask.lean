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

def andThen (self : IOTask α) (act : IO β) (prio := Task.Priority.dedicated) : IO (IOTask β) :=
  IO.mapTask (fun x => IO.ofExcept x *> act) self prio

instance : HAndThen (IOTask α) (IO β) (IO (IOTask β)) := ⟨andThen⟩

def bindAsync (self : IOTask α) (f : α → IO (IOTask β)) (prio := Task.Priority.dedicated) : IO (IOTask β) :=
  IO.bindTask self (fun x => do let x ← IO.ofExcept x; f x)  prio

instance : MonadAsync IO IOTask where
  async := IOTask.spawn
  await := IOTask.await
  mapAsync := IOTask.mapAsync
  bindAsync := IOTask.bindAsync

end IOTask


-- # Build Task

def BuildTask := IOTask PUnit

namespace BuildTask

def nop : BuildTask :=
  Task.pure (Except.ok ())

def spawn (act : IO PUnit) (prio := Task.Priority.dedicated) : IO BuildTask :=
  IO.asTask act prio

def all (tasks : List BuildTask) (prio := Task.Priority.dedicated)  : IO BuildTask :=
  IO.asTask (tasks.forM (·.await)) prio

end BuildTask

instance : Inhabited BuildTask := ⟨BuildTask.nop⟩

def afterTaskList (tasks : List BuildTask) (act : IO PUnit) : IO BuildTask :=
  afterListAsync (async act) tasks

def afterTaskArray (tasks : Array BuildTask) (act : IO PUnit) : IO BuildTask :=
  afterArrayAsync (async act) tasks

instance : HAndThen BuildTask (IO PUnit) (IO BuildTask) :=
  ⟨IOTask.andThen⟩

instance : HAndThen (List BuildTask) (IO PUnit) (IO BuildTask) :=
  ⟨afterTaskList⟩

instance : HAndThen (Array BuildTask) (IO PUnit) (IO BuildTask) :=
  ⟨afterTaskArray⟩
