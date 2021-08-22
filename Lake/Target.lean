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

structure TargetInfo.{u,v,w} (t : Type u) (m : Type v) (a : Type w) where
  artifact  : a
  trace     : t
  task      : m

namespace TargetInfo

def withArtifact (artifact : a) (self : TargetInfo t m b) : TargetInfo t m a :=
  {self with artifact}

def withoutArtifact (self : TargetInfo t m a) : TargetInfo t m PUnit :=
  self.withArtifact ()

def withTrace (trace : t) (self : TargetInfo r m a) : TargetInfo t m a :=
  {self with trace}

def withoutTrace (self : TargetInfo t m a) : TargetInfo PUnit m a :=
  self.withTrace ()

def withTask (task : m) (self : TargetInfo t n a) : TargetInfo t m a :=
  {self with task}

def mtime (self : TargetInfo MTime m a) : MTime :=
  self.trace

def file (self : TargetInfo t m FilePath) : FilePath :=
  self.artifact

def filesList (self : TargetInfo t m (List FilePath)) : List FilePath :=
  self.artifact

def filesArray (self : TargetInfo t m (Array FilePath)) : Array FilePath :=
  self.artifact

end TargetInfo

--------------------------------------------------------------------------------
-- # Active Targets
--------------------------------------------------------------------------------

def ActiveTarget.{u,v,v',w} (t : Type u) (m : Type v → Type v') (a : Type w) :=
  TargetInfo t (m PUnit) a

instance [Inhabited t] [Inhabited a] [Pure m] : Inhabited (ActiveTarget t m a) :=
  ⟨Inhabited.default, Inhabited.default, pure ()⟩

namespace ActiveTarget

def mk (artifact : a) (trace : t) (task : m PUnit) : ActiveTarget t m a :=
  ⟨artifact, trace, task⟩

protected def pure [Pure m] (artifact : a) (trace : t) : ActiveTarget t m a :=
  ⟨artifact, trace, pure ()⟩

def materialize [Await n m] (self : ActiveTarget t n α) : m PUnit :=
  await self.task

-- ## Opaque Active Targets

def opaque (trace : t) (task : m PUnit) : ActiveTarget t m PUnit :=
  ⟨(), trace, task⟩

section
variable [NilTrace t] [MixTrace t] [Monad m] [Pure n] [BindAsync m n] [Async m n]

def collectOpaqueList (targets : List (ActiveTarget t n a)) : m (ActiveTarget t n PUnit) := do
  let task ← joinTaskList <| targets.map (·.task)
  let trace := mixTraceList <| targets.map (·.trace)
  ActiveTarget.opaque trace task

def collectOpaqueArray (targets : Array (ActiveTarget t n a)) : m (ActiveTarget t n PUnit) := do
  let task ← joinTaskArray <| targets.map (·.task)
  let trace := mixTraceArray <| targets.map (·.trace)
  ActiveTarget.opaque trace task

end

-- ## Sequencing

section
variable [SeqRightAsync m n]

def andThen (target : ActiveTarget t n a) (act : m PUnit) : m (n PUnit) :=
  seqRightAsync target.task act

instance  : HAndThen (ActiveTarget t n a) (m PUnit) (m (n PUnit)) := ⟨andThen⟩
end

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

def Target.{u,v,v',v'',w} (t : Type u) (m : Type v' → Type v'') (n : Type v → Type v') (a : Type w) :=
  TargetInfo t (m (n PUnit)) a

instance [Inhabited t] [Inhabited a] [Pure m] [Pure n] : Inhabited (Target t m n a) :=
  ⟨Inhabited.default, Inhabited.default, pure (pure ())⟩

namespace Target

def mk (artifact : a) (trace : t) (task : m (n PUnit)) : Target t m n a :=
  ⟨artifact, trace, task⟩

protected def pure [Pure m] [Pure n] (artifact : a) (trace : t) : Target t m n a :=
  ⟨artifact, trace, pure (pure ())⟩

def compute [ComputeTrace a m' t] [Monad m'] [Pure m] [Pure n] (artifact : a) : m' (Target t m n a) := do
  Target.pure artifact <| ← computeTrace artifact

-- ## Materializing

def run [Monad m] (self : Target t m n a) : m (ActiveTarget t n a) := do
  self.withTask <| ← self.task

def materializeAsync (self : Target t m n a) : m (n PUnit) :=
  self.task

def materialize [Await n m] [Bind m] (self : Target t m n a) : m PUnit := do
  await <| ← self.task

section
variable [Monad m] [Pure n] [BindAsync m n] [Async m n]

def materializeListAsync  (targets : List (Target t m n a)) : m (n PUnit) := do
  joinTaskList (← targets.mapM (·.materializeAsync))

def materializeList [Await n m] (targets : List (Target t m n a)) : m PUnit := do
  await <| ← materializeListAsync targets

def materializeArrayAsync (targets : Array (Target t m n a)) :  m (n PUnit) := do
  joinTaskArray (← targets.mapM (·.materializeAsync))

def materializeArray [Await n m] (targets : Array (Target t m n a)) :  m PUnit := do
  await <| ← materializeArrayAsync targets

end

-- ## Opaque Targets

def opaque (trace : t) (task : m (n PUnit)) : Target t m n PUnit :=
  ⟨(), trace, task⟩

section
variable [NilTrace t] [MixTrace t] [Monad m] [Pure n] [BindAsync m n] [Async m n]

def collectOpaqueList (targets : List (Target t m n a)) : Target t m n PUnit :=
  let trace := mixTraceList <| targets.map (·.trace)
  Target.opaque trace do Target.materializeListAsync targets

def collectOpaqueArray (targets : Array (Target t m n a)) : Target t m n PUnit :=
  let trace := mixTraceArray <| targets.map (·.trace)
  Target.opaque trace do Target.materializeArrayAsync targets

end

-- ## Sequencing

section
variable [SeqRightAsync m n] [Bind m]

def andThen (target : Target t m n a) (act : m β) : m (n β) := do
  seqRightAsync (← target.materializeAsync) act

instance : HAndThen (Target t m n a) (m β) (m (n β)) := ⟨andThen⟩
end

end Target

-- ## Combinators

section
variable [Monad m] [BindAsync m n] [Async m n]

def afterTargetList (targets : List (Target t m n a)) (act : m PUnit) : m (n PUnit) := do
  afterTaskList (← targets.mapM (·.materializeAsync)) act

def afterTargetArray (targets : Array (Target t m n a)) (act : m PUnit) : m (n PUnit) := do
  afterTaskArray (← targets.mapM (·.materializeAsync)) act

instance : HAndThen (List (Target t m n a)) (m PUnit) (m (n PUnit)) := ⟨afterTargetList⟩
instance : HAndThen (Array (Target t m n a)) (m PUnit) (m (n PUnit)) := ⟨afterTargetArray⟩
end
