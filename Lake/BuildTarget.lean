/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.BuildTask
import Lake.BuildTrace

namespace Lake

-- # Build Target

structure BuildTarget (t : Type) (a : Type) where
  artifact    : a
  trace       : t
  buildTask   : BuildTask

-- manually derive `Inhabited` instance because automatic deriving fails
instance [Inhabited t] [Inhabited a] : Inhabited (BuildTarget t a) :=
  ⟨Inhabited.default, Inhabited.default, BuildTask.nop⟩

namespace BuildTarget

def pure (artifact : a) (trace : t) : BuildTarget t a :=
  {artifact, trace, buildTask := BuildTask.nop}

def withTrace (trace : t) (self : BuildTarget r a) : BuildTarget t a :=
  {self with trace := trace}

def discardTrace (self : BuildTarget t a) : BuildTarget PUnit a :=
  self.withTrace ()

def withArtifact (artifact : a) (self : BuildTarget t b) : BuildTarget t a :=
  {self with artifact := artifact}

def discardArtifact (self : BuildTarget t α) : BuildTarget t PUnit :=
  self.withArtifact ()

def materialize (self : BuildTarget t α) : IO PUnit :=
  self.buildTask.await

end BuildTarget

def afterTarget (target : BuildTarget t a) (act : IO PUnit)  : IO BuildTask :=
  afterTask target.buildTask act

def afterTargetList (targets : List (BuildTarget t a)) (act : IO PUnit) : IO BuildTask :=
  afterTaskList (targets.map (·.buildTask)) act

instance : HAndThen (BuildTarget t a) (IO PUnit) (IO BuildTask) :=
  ⟨afterTarget⟩

instance : HAndThen (List (BuildTarget t a)) (IO PUnit) (IO BuildTask) :=
  ⟨afterTargetList⟩

-- # MTIme Build Target

abbrev MTimeBuildTarget := BuildTarget MTime

namespace MTimeBuildTarget

def mtime (self : MTimeBuildTarget a) :=
  self.trace

def mk (artifact : a) (mtime : MTime := 0) (buildTask : BuildTask) : MTimeBuildTarget a :=
  {artifact, trace := mtime, buildTask}

def pure (artifact : a) (mtime : MTime := 0) : MTimeBuildTarget a :=
  {artifact, trace := mtime, buildTask := BuildTask.nop}

def all (targets : List (MTimeBuildTarget a)) : IO (MTimeBuildTarget PUnit) := do
  let depsMTime := MTime.listMax <| targets.map (·.mtime)
  let task ← BuildTask.all <| targets.map (·.buildTask)
  return MTimeBuildTarget.mk () depsMTime task

def collectAll (targets : List (MTimeBuildTarget a)) : IO (MTimeBuildTarget (List a)) := do
  let artifacts := targets.map (·.artifact)
  let depsMTime := MTime.listMax <|  targets.map (·.mtime)
  let task ← BuildTask.all <| targets.map (·.buildTask)
  return MTimeBuildTarget.mk artifacts depsMTime task

end MTimeBuildTarget
