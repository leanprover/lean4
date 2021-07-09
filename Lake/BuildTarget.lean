/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/

namespace Lake

def BuildTask := Task (Except IO.Error PUnit)

namespace BuildTask

def nop : BuildTask := 
  Task.pure (Except.ok ())

def await (self : BuildTask) : IO PUnit := do
  IO.ofExcept (← IO.wait self)

end BuildTask

instance : Inhabited BuildTask := ⟨BuildTask.nop⟩

structure BuildTarget (α : Type) where
  artifact    : α
  maxMTime    : IO.FS.SystemTime
  buildTask   : BuildTask

-- manually derive `Inhabited` instance because automatic deriving fails
instance [Inhabited α] : Inhabited (BuildTarget α) := 
  ⟨Inhabited.default, Inhabited.default, BuildTask.nop⟩

namespace BuildTarget

def pure (artifact : α) (maxMTime : IO.FS.SystemTime := ⟨0, 0⟩) : BuildTarget α :=
  {artifact, maxMTime, buildTask := BuildTask.nop}

def afterBuild (action : IO PUnit) (self : BuildTarget α) : IO BuildTask :=
  IO.mapTask (fun x => IO.ofExcept x *> action) self.buildTask

def materialize (self : BuildTarget α) : IO PUnit :=
  self.buildTask.await

end BuildTarget

namespace BuildTask

def afterTargets 
(targets : List (BuildTarget α)) (action : IO PUnit) : IO BuildTask := do
  let tasks ← targets.mapM (·.buildTask)
  IO.mapTasks (tasks := tasks) fun xs => xs.forM IO.ofExcept *> action

end BuildTask
