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

def all (tasks : List BuildTask) : IO BuildTask :=
  IO.asTask (tasks.forM (·.await))

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

def all (targets : List (BuildTarget α)) : IO (BuildTarget PUnit) := do
  let depsMTime := targets.map (·.maxMTime) |>.maximum? |>.getD ⟨0, 0⟩
  let task ← BuildTask.all <| targets.map (·.buildTask)
  BuildTarget.mk () depsMTime task

def collectAll (targets : List (BuildTarget α)) : IO (BuildTarget (List α)) := do
  let artifacts := targets.map (·.artifact)
  let depsMTime := targets.map (·.maxMTime) |>.maximum? |>.getD ⟨0, 0⟩
  let task ← BuildTask.all <| targets.map (·.buildTask)
  BuildTarget.mk artifacts depsMTime task

def withArtifact (artifact : α) (self : BuildTarget β) : BuildTarget α :=
  {self with artifact := artifact}

def discardArtifact (self : BuildTarget α) : BuildTarget PUnit :=
  self.withArtifact ()

def materialize (self : BuildTarget α) : IO PUnit :=
  self.buildTask.await

end BuildTarget

namespace BuildTask

def afterTarget (target : BuildTarget α) (action : IO PUnit)  : IO BuildTask :=
  IO.mapTask (fun x => IO.ofExcept x *> action) target.buildTask

def afterTargets (targets : List (BuildTarget α)) (action : IO PUnit) : IO BuildTask := do
  IO.mapTasks (fun xs => xs.forM IO.ofExcept *> action) <| targets.map (·.buildTask)

end BuildTask
