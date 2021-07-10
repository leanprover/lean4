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

namespace BuildTask

def afterTarget (target : BuildTarget t a) (action : IO PUnit)  : IO BuildTask :=
  IO.mapTask (fun x => IO.ofExcept x *> action) target.buildTask

def afterTargets (targets : List (BuildTarget t a)) (action : IO PUnit) : IO BuildTask := do
  IO.mapTasks (fun xs => xs.forM IO.ofExcept *> action) <| targets.map (·.buildTask)

end BuildTask

-- # MTime Build Targets

section
open IO.FS (SystemTime)

def MTime := SystemTime

instance : Inhabited MTime := ⟨⟨0,0⟩⟩
instance : OfNat MTime (nat_lit 0) := ⟨⟨0,0⟩⟩
instance : BEq MTime := inferInstanceAs (BEq SystemTime)
instance : Repr MTime := inferInstanceAs (Repr SystemTime)
instance : Ord MTime := inferInstanceAs (Ord SystemTime)
instance : LT MTime := ltOfOrd
instance : LE MTime := leOfOrd
end

def MTime.listMax (mtimes : List MTime) := mtimes.maximum?.getD 0

class GetMTime (α) where
  getMTime : α → IO MTime

export GetMTime (getMTime)

instance : GetMTime System.FilePath where
  getMTime file := do (← file.metadata).modified

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
