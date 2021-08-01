/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.BuildTask
import Lake.BuildTrace

namespace Lake

-- # Active Build Target

structure ActiveBuildTarget (t : Type) (a : Type) where
  artifact  : a
  trace     : t
  task      : BuildTask

-- manually derive `Inhabited` instance because automatic deriving fails
instance [Inhabited t] [Inhabited a] : Inhabited (ActiveBuildTarget t a) :=
  ⟨Inhabited.default, Inhabited.default, BuildTask.nop⟩

namespace ActiveBuildTarget

def nil [Inhabited t] : ActiveBuildTarget t PUnit :=
  ⟨(), Inhabited.default, BuildTask.nop⟩

def pure (artifact : a) (trace : t) : ActiveBuildTarget t a :=
  ⟨artifact, trace, BuildTask.nop⟩

def opaque (trace : t) (task : BuildTask) : ActiveBuildTarget t PUnit :=
  ⟨(), trace, task⟩

def withTrace (trace : t) (self : ActiveBuildTarget r a) : ActiveBuildTarget t a :=
  {self with trace := trace}

def discardTrace (self : ActiveBuildTarget t a) : ActiveBuildTarget PUnit a :=
  self.withTrace ()

def mtime (self : ActiveBuildTarget MTime a) : MTime :=
  self.trace

def withArtifact (artifact : a) (self : ActiveBuildTarget t b) : ActiveBuildTarget t a :=
  {self with artifact := artifact}

def discardArtifact (self : ActiveBuildTarget t α) : ActiveBuildTarget t PUnit :=
  self.withArtifact ()

def materialize (self : ActiveBuildTarget t α) : IO PUnit :=
  self.task.await

end ActiveBuildTarget

def afterTarget (target : ActiveBuildTarget t a) (act : IO PUnit)  : IO BuildTask :=
  afterTask target.task act

def afterTargetList (targets : List (ActiveBuildTarget t a)) (act : IO PUnit) : IO BuildTask :=
  afterTaskList (targets.map (·.task)) act

instance : HAndThen (ActiveBuildTarget t a) (IO PUnit) (IO BuildTask) :=
  ⟨afterTarget⟩

instance : HAndThen (List (ActiveBuildTarget t a)) (IO PUnit) (IO BuildTask) :=
  ⟨afterTargetList⟩

-- # File Target

open System

abbrev ActiveFileTarget := ActiveBuildTarget MTime FilePath

namespace ActiveFileTarget

def mk (file : FilePath) (depMTime : MTime) (task : BuildTask) :=
  ActiveBuildTarget.mk file depMTime task

def pure (file : FilePath) (depMTime : MTime) :=
  ActiveBuildTarget.pure file depMTime

end ActiveFileTarget

-- # Lean Target

abbrev LeanTarget a := ActiveBuildTarget LeanTrace a

namespace LeanTarget

def hash (self : LeanTarget a) := self.trace.hash
def mtime (self : LeanTarget a) := self.trace.mtime

def all (targets : List (LeanTarget a)) : IO (LeanTarget PUnit) := do
  let hash := Hash.foldList 0 <| targets.map (·.hash)
  let mtime := MTime.listMax <| targets.map (·.mtime)
  let task ← BuildTask.all <| targets.map (·.task)
  return ActiveBuildTarget.mk () ⟨hash, mtime⟩ task

def fromMTimeTarget (target : ActiveBuildTarget MTime a) : LeanTarget a :=
  {target with trace := LeanTrace.fromMTime target.trace}

end LeanTarget
