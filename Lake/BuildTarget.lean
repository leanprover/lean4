/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.BuildTask
import Lake.BuildTrace

open System
namespace Lake

--------------------------------------------------------------------------------
-- # Target Structure
--------------------------------------------------------------------------------

structure BaseTarget.{u,v} (t : Type u) (m : Type u → Type v) (a : Type u) where
  artifact  : a
  trace     : t
  task      : m PUnit

instance [Inhabited t] [Inhabited a] [Pure m] : Inhabited (BaseTarget t m a) :=
  ⟨Inhabited.default, Inhabited.default, pure ()⟩

namespace BaseTarget

def withArtifact (artifact : a) (self : BaseTarget t m b) : BaseTarget t m a :=
  {self with artifact}

def withoutArtifact (self : BaseTarget t m a) : BaseTarget t m PUnit :=
  self.withArtifact ()

def withTrace (trace : t) (self : BaseTarget r m a) : BaseTarget t m a :=
  {self with trace}

def withoutTrace (self : BaseTarget t m a) : BaseTarget PUnit m a :=
  self.withTrace ()

def withTask (task : m PUnit) (self : BaseTarget t n a) : BaseTarget t m a :=
  {self with task}

def mtime (self : BaseTarget MTime m a) : MTime :=
  self.trace

def file (self : BaseTarget t m FilePath) : FilePath :=
  self.artifact

def filesList (self : BaseTarget t m (List FilePath)) : List FilePath :=
  self.artifact

def filesArray (self : BaseTarget t m (Array FilePath)) : Array FilePath :=
  self.artifact

end BaseTarget

--------------------------------------------------------------------------------
-- # Active Targets
--------------------------------------------------------------------------------

def ActiveTarget t m a :=
  BaseTarget t m a

instance [Inhabited t] [Inhabited a] [Pure m] : Inhabited (ActiveTarget t m a) :=
  ⟨Inhabited.default, Inhabited.default, pure ()⟩

namespace ActiveTarget

def mk (artifact : a) (trace : t) (task : m PUnit) : ActiveTarget t m a :=
  ⟨artifact, trace, task⟩

def opaque (trace : t) (task : m PUnit) : ActiveTarget t m PUnit :=
  ⟨(), trace, task⟩

protected def pure [Pure m] (artifact : a) (trace : t) : ActiveTarget t m a :=
  ⟨artifact, trace, pure ()⟩

def nil [Pure m] [Inhabited t] : ActiveTarget t m PUnit :=
  ActiveTarget.pure () Inhabited.default

def materialize [Await m n] (self : ActiveTarget t n α) : m PUnit :=
  await self.task

end ActiveTarget

-- ## Active Build Target

abbrev ActiveBuildTarget t a :=
  ActiveTarget t IOTask a

namespace ActiveBuildTarget

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

--------------------------------------------------------------------------------
-- # Inactive Target
--------------------------------------------------------------------------------

def Target t m a :=
  BaseTarget t m a

instance [Inhabited t] [Inhabited a] [Pure m] : Inhabited (ActiveTarget t m a) :=
  ⟨Inhabited.default, Inhabited.default, pure ()⟩

namespace Target

def mk (artifact : a) (trace : t) (task : m PUnit) : Target t m a :=
  ⟨artifact, trace, task⟩

def opaque (trace : t) (task : m PUnit) : Target t m PUnit :=
  ⟨(), trace, task⟩

protected def pure [Pure m] (artifact : a) (trace : t) : Target t m a :=
  ⟨artifact, trace, pure ()⟩

def runAsync [Monad m] [Async m n] (self : Target t m a) : m (ActiveTarget t n a) := do
  self.withTask <| ← async self.task

def materializeAsync [Async m n] (self : Target t m a) : m (n PUnit) :=
  async self.task

def materialize (self : Target t m a) : m PUnit :=
  self.task

def materializeList [Monad m] [MonadAsync m n] (targets : List (Target t m a)) : m PUnit := do
  (← targets.mapM (·.materializeAsync)).forM await

def materializeArray [Monad m] [MonadAsync m n] (targets : Array (Target t m a)) : m PUnit := do
  (← targets.mapM (·.materializeAsync)).forM await

end Target

-- ## BuildTarget

abbrev BuildTarget t a :=
  Target t IO a

--------------------------------------------------------------------------------
-- # File Targets
--------------------------------------------------------------------------------

-- ## File BaseTarget

abbrev FileTarget :=
  BuildTarget MTime FilePath

namespace FileTarget

def mk (file : FilePath) (depMTime : MTime) (task : IO PUnit) : FileTarget :=
  ⟨file, depMTime, task⟩

def compute (file : FilePath) : IO FileTarget := do
  Target.pure file (← getMTime file)

end FileTarget

-- ## Files BaseTarget

abbrev FilesTarget :=
  BuildTarget MTime (Array FilePath)

namespace FilesTarget

def files (self : FilesTarget) : Array FilePath :=
  self.artifact

def filesAsList (self : FilesTarget) : List FilePath :=
  self.artifact.toList

def filesAsArray (self : FilesTarget) : Array FilePath :=
  self.artifact

def compute (files : Array FilePath) : IO FilesTarget := do
  Target.pure files (MTime.arrayMax <| ← files.mapM getMTime)

def singleton (target : FileTarget) : FilesTarget :=
  target.withArtifact #[target.file]

def collectList (targets : List FileTarget) : FilesTarget :=
  let files := Array.mk <| targets.map (·.file)
  let mtime := MTime.listMax <| targets.map (·.mtime)
  Target.mk files mtime do Target.materializeList targets

def collectArray (targets : Array FileTarget) : FilesTarget :=
  let files := targets.map (·.file)
  let mtime := MTime.arrayMax <| targets.map (·.mtime)
  Target.mk files mtime do Target.materializeArray targets

def collect (targets : Array FileTarget) : FilesTarget :=
  collectArray targets

end FilesTarget

instance : Coe FileTarget FilesTarget := ⟨FilesTarget.singleton⟩
instance : Coe (List FileTarget) FilesTarget := ⟨FilesTarget.collectList⟩
instance : Coe (Array FileTarget) FilesTarget := ⟨FilesTarget.collectArray⟩

-- ## Active File Target

abbrev ActiveFileTarget :=
  ActiveBuildTarget MTime FilePath

namespace ActiveFileTarget

def mk (file : FilePath) (depMTime : MTime) (task : BuildTask) : ActiveFileTarget :=
  ActiveTarget.mk file depMTime task

end ActiveFileTarget

--------------------------------------------------------------------------------
-- # Lake Target
--------------------------------------------------------------------------------

abbrev LakeTarget a :=
  ActiveBuildTarget LakeTrace a

namespace LakeTarget

def nil : LakeTarget PUnit :=
  ActiveTarget.pure () Inhabited.default

def hash (self : LakeTarget a) := self.trace.hash
def mtime (self : LakeTarget a) := self.trace.mtime

def all (targets : List (LakeTarget a)) : IO (LakeTarget PUnit) := do
  let hash := Hash.foldList 0 <| targets.map (·.hash)
  let mtime := MTime.listMax <| targets.map (·.mtime)
  let task ← BuildTask.all <| targets.map (·.task)
  return ActiveTarget.mk () ⟨hash, mtime⟩ task

def fromMTimeTarget (target : ActiveBuildTarget MTime a) : LakeTarget a :=
  {target with trace := LakeTrace.fromMTime target.trace}

def buildOpaqueFromFileTarget (target : FileTarget) : IO (LakeTarget PUnit) := do
  LakeTarget.fromMTimeTarget <| ← Target.runAsync target.withoutArtifact

end LakeTarget
