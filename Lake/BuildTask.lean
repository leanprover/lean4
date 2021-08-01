/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/

namespace Lake

instance : Monad Task where
  map := Task.map
  pure := Task.pure
  bind := Task.bind

abbrev ETask ε α := ExceptT ε Task α

abbrev IOTask α := ETask IO.Error α

namespace IOTask

def spawn (act : IO α) (prio := Task.Priority.default) : IO (IOTask α) :=
  IO.asTask act prio

def await (self : IOTask α) : IO α := do
  IO.ofExcept (← IO.wait self)

def collectAll (tasks : List (IOTask α)) : IO (IOTask (List α)) :=
  IO.asTask (tasks.mapM (·.await))

end IOTask

def BuildTask := IOTask PUnit

namespace BuildTask

def nop : BuildTask :=
  Task.pure (Except.ok ())

def spawn (act : IO PUnit) (prio := Task.Priority.dedicated) : IO BuildTask :=
  IO.asTask act prio

def all (tasks : List BuildTask) (prio := Task.Priority.default)  : IO BuildTask :=
  IO.asTask (tasks.forM (·.await)) prio

end BuildTask

instance : Inhabited BuildTask := ⟨BuildTask.nop⟩

def afterTask (task : BuildTask) (act : IO PUnit)  : IO BuildTask :=
  IO.mapTask (fun x => IO.ofExcept x *> act) task

def afterTaskList (tasks : List BuildTask) (act : IO PUnit) : IO BuildTask :=
  IO.mapTasks (fun xs => xs.forM IO.ofExcept *> act) tasks

instance : HAndThen BuildTask (IO PUnit) (IO BuildTask) :=
  ⟨afterTask⟩

instance : HAndThen (List BuildTask) (IO PUnit) (IO BuildTask) :=
  ⟨afterTaskList⟩
