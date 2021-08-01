/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.BuildTask
import Lake.BuildTrace

namespace Lake

--------------------------------------------------------------------------------
-- # Target
--------------------------------------------------------------------------------

structure Target (t : Type) (m : Type) (a : Type) where
  artifact  : a
  trace     : t
  task      : m
  deriving Inhabited

namespace Target

def withTrace (trace : t) (self : Target r m a) : Target t m a :=
  {self with trace := trace}

def discardTrace (self : Target t m a) : Target PUnit m a :=
  self.withTrace ()

def withArtifact (artifact : a) (self : Target t m b) : Target t m a :=
  {self with artifact := artifact}

def discardArtifact (self : Target t m α) : Target t m PUnit :=
  self.withArtifact ()

def mtime (self : Target MTime m a) : MTime :=
  self.trace

end Target

--------------------------------------------------------------------------------
-- # Build Targets
--------------------------------------------------------------------------------

-- ## Active Build Target

abbrev ActiveBuildTarget (t : Type) (a : Type) := Target t BuildTask a

namespace ActiveBuildTarget

def mk (artifact : a) (trace : t) (task : BuildTask) : ActiveBuildTarget t a :=
  ⟨artifact, trace, task⟩

def opaque (trace : t) (task : BuildTask) : ActiveBuildTarget t PUnit :=
  ⟨(), trace, task⟩

def pure (artifact : a) (trace : t) : ActiveBuildTarget t a :=
  ⟨artifact, trace, BuildTask.nop⟩

def nil [Inhabited t] : ActiveBuildTarget t PUnit :=
  pure () Inhabited.default

def materialize (self : ActiveBuildTarget t α) : IO PUnit :=
  self.task.await

-- ### Combinators

def after (target : ActiveBuildTarget t a) (act : IO PUnit)  : IO BuildTask :=
  afterTask target.task act

def afterList (targets : List (ActiveBuildTarget t a)) (act : IO PUnit) : IO BuildTask :=
  afterTaskList (targets.map (·.task)) act

instance : HAndThen (ActiveBuildTarget t a) (IO PUnit) (IO BuildTask) :=
  ⟨ActiveBuildTarget.after⟩

instance : HAndThen (List (ActiveBuildTarget t a)) (IO PUnit) (IO BuildTask) :=
  ⟨ActiveBuildTarget.afterList⟩

end ActiveBuildTarget

-- ## Build Target

abbrev BuildTarget (t : Type) (a : Type) := Target t (IO BuildTask) a

namespace BuildTarget

def mk (artifact : a) (trace : t) (task : IO BuildTask) : BuildTarget t a :=
  ⟨artifact, trace, task⟩

def opaque (trace : t) (task : IO BuildTask) : BuildTarget t PUnit :=
  ⟨(), trace, task⟩

def pure (artifact : a) (trace : t) : BuildTarget t a :=
  ⟨artifact, trace, BuildTask.nop⟩

def nil [Inhabited t] : BuildTarget t PUnit :=
  pure () Inhabited.default

def spawn (self : BuildTarget t a) : IO (ActiveBuildTarget t a) := do
  return {self with task := (← self.task)}

def materialize (self : BuildTarget t a) : IO PUnit := do
  (← self.task).await

end BuildTarget

--------------------------------------------------------------------------------
-- # File Targets
--------------------------------------------------------------------------------

section
open System

-- ## File Target

abbrev FileTarget := BuildTarget MTime FilePath

namespace FileTarget

def mk (file : FilePath) (depMTime : MTime) (task : IO BuildTask) : FileTarget :=
  ⟨file, depMTime, task⟩

def pure (file : FilePath) (depMTime : MTime) : FileTarget :=
  BuildTarget.pure file depMTime

end FileTarget

-- ## Active File Target

abbrev ActiveFileTarget := ActiveBuildTarget MTime FilePath

namespace ActiveFileTarget

def mk (file : FilePath) (depMTime : MTime) (task : BuildTask) : ActiveFileTarget :=
  ActiveBuildTarget.mk file depMTime task

def pure (file : FilePath) (depMTime : MTime) : ActiveFileTarget :=
  ActiveBuildTarget.pure file depMTime

end ActiveFileTarget

end

--------------------------------------------------------------------------------
-- # Lean Target
--------------------------------------------------------------------------------

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
