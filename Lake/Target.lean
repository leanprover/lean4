/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Task
import Lake.Trace

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

def materialize [Await n m] (self : ActiveTarget t n α) : m PUnit :=
  await self.task

def andThen [SeqRightAsync m n] (target : ActiveTarget t n a) (act : m PUnit) : m (n PUnit) :=
  seqRightAsync target.task act

instance [SeqRightAsync m n] : HAndThen (ActiveTarget t n a) (m PUnit) (m (n PUnit)) :=
  ⟨andThen⟩

def all [Monad m] [Pure n] [BindAsync m n] [Async m n] [NilTrace t] [MixTrace t]
  (targets : List (ActiveTarget t n a)) : m (ActiveTarget t n PUnit) := do
  let task ← joinTaskList <| targets.map (·.task)
  let trace := mixTraceList <| targets.map (·.trace)
  return ActiveTarget.mk () trace task

end ActiveTarget

-- ## Combinators

section
variable [Monad m] [BindAsync m n] [Async m n]

def afterActiveList (targets : List (ActiveTarget t n a)) (act : m PUnit) : m (n PUnit) :=
  afterTaskList (targets.map (·.task)) act

def afterActiveArray (targets : Array (ActiveTarget t n a)) (act : m PUnit) : m (n PUnit) :=
  afterTaskArray (targets.map (·.task)) act

instance : HAndThen (List (ActiveTarget t n a)) (m PUnit) (m (n PUnit)) :=
  ⟨afterActiveList⟩

instance : HAndThen (Array (ActiveTarget t n a)) (m PUnit) (m (n PUnit)) :=
  ⟨afterActiveArray⟩

end

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

def compute [Monad m] [ComputeTrace a m t] (artifact : a) : m (Target t m a) := do
  Target.pure artifact <| ← computeTrace artifact

def runAsync [Monad m] [Async m n] (self : Target t m a) : m (ActiveTarget t n a) := do
  self.withTask <| ← async self.task

def materializeAsync [Async m n] (self : Target t m a) : m (n PUnit) :=
  async self.task

def materialize (self : Target t m a) : m PUnit :=
  self.task

section
variable [Monad m] [Pure n] [BindAsync m n] [Async m n]

def materializeListAsync  (targets : List (Target t m a)) : m (n PUnit) := do
  joinTaskList (← targets.mapM (·.materializeAsync))

def materializeList [Await n m] (targets : List (Target t m a)) : m PUnit := do
  await <| ← materializeListAsync targets

def materializeArrayAsync [Await n m] (targets : Array (Target t m a)) :  m (n PUnit) := do
  joinTaskArray (← targets.mapM (·.materializeAsync))

def materializeArray [Await n m] (targets : Array (Target t m a)) :  m PUnit := do
  await <| ← materializeArrayAsync targets

end

def andThen [SeqRight m] (target : Target t m a) (act : m β) : m β :=
  target.task *> act

instance [SeqRight m] : HAndThen (Target t m a) (m β) (m β) := ⟨andThen⟩

end Target

--------------------------------------------------------------------------------
-- # Build Targets
--------------------------------------------------------------------------------

-- ## Inactive Target

abbrev LakeTarget a :=
  Target LakeTrace IO a

namespace LakeTarget

def nil : LakeTarget PUnit :=
  Target.pure () LakeTrace.nil

def hash (self : LakeTarget a) := self.trace.hash
def mtime (self : LakeTarget a) := self.trace.mtime

end LakeTarget

-- ## Active Target

abbrev ActiveLakeTarget a :=
  ActiveTarget LakeTrace IOTask a

namespace ActiveLakeTarget

def nil : ActiveLakeTarget PUnit :=
  ActiveTarget.pure () LakeTrace.nil

def hash (self : ActiveLakeTarget a) := self.trace.hash
def mtime (self : ActiveLakeTarget a) := self.trace.mtime

end ActiveLakeTarget

--------------------------------------------------------------------------------
-- # File Targets
--------------------------------------------------------------------------------

-- ## File Target

abbrev FileTarget :=
  LakeTarget FilePath

namespace FileTarget

def compute (file : FilePath) : IO FileTarget :=
  Target.compute file

end FileTarget

-- ## Active File Target

abbrev ActiveFileTarget :=
  ActiveLakeTarget FilePath
