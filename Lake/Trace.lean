/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/

open System
namespace Lake

--------------------------------------------------------------------------------
-- # Trace Abstraction
--------------------------------------------------------------------------------

class ComputeTrace.{u,v,w} (i : Type u) (m : outParam $ Type v → Type w) (t : Type v) where
  /-- Compute the trace of some info using information from the monadic context. -/
  computeTrace : i → m t

export ComputeTrace (computeTrace)

class NilTrace.{u} (t : Type u) where
  /-- The nil trace. Should not unduly clash with a proper trace. -/
  nilTrace : t

export NilTrace (nilTrace)

instance [NilTrace t] : Inhabited t := ⟨nilTrace⟩

class MixTrace.{u} (t : Type u) where
  /--
    Combine two traces.
    The result should be dirty if either of the inputs is dirty.
  -/
  mixTrace : t → t → t

export MixTrace (mixTrace)

def mixTraceM [MixTrace t] [Pure m] (t1 t2 : t) : m t :=
  pure <| mixTrace t1 t2

section
variable [MixTrace t] [NilTrace t]

def mixTraceList (traces : List t) : t :=
  traces.foldl mixTrace nilTrace

def mixTraceArray (traces : Array t) : t :=
  traces.foldl mixTrace nilTrace

variable [ComputeTrace i m t] [Monad m]

def computeListTrace  (artifacts : List i) : m t :=
  mixTraceList <$> artifacts.mapM computeTrace

instance : ComputeTrace (List i) m t := ⟨computeListTrace⟩

def computeArrayTrace (artifacts : Array i) : m t :=
  mixTraceArray <$> artifacts.mapM computeTrace

instance : ComputeTrace (Array i) m t := ⟨computeArrayTrace⟩
end

--------------------------------------------------------------------------------
-- # Hash Trace
--------------------------------------------------------------------------------

/--
  A content hash.
  TODO: Use a secure hash rather than the builtin Lean hash function.
-/
structure Hash where
  val : UInt64
  deriving BEq, DecidableEq, Repr

namespace Hash

def ofNat (n : Nat) :=
  mk n.toUInt64

def fromFile (hashFile : FilePath) : IO (Option Hash) := do
  (← IO.FS.readFile hashFile).toNat?.map Hash.ofNat

def nil : Hash :=
  mk <| 1723 -- same as Name.anonymous

instance : NilTrace Hash := ⟨nil⟩

def compute (str : String) :=
  mk <| mixHash 1723 (hash str) -- same as Name.mkSimple

def mix (h1 h2 : Hash) : Hash :=
  mk <| mixHash h1.val h2.val

instance : MixTrace Hash := ⟨mix⟩

protected def toString (self : Hash) : String :=
  toString self.val

instance : ToString Hash := ⟨Hash.toString⟩

end Hash

class ComputeHash (α) where
  computeHash : α → IO Hash

export ComputeHash (computeHash)
instance [ComputeHash α] : ComputeTrace α IO Hash := ⟨computeHash⟩

def getFileHash (file : FilePath) : IO Hash :=
  Hash.compute <$> IO.FS.readFile file

instance : ComputeHash FilePath := ⟨getFileHash⟩
instance : ComputeHash String := ⟨pure ∘ Hash.compute⟩

--------------------------------------------------------------------------------
-- # Modification Time (MTime) Trace
--------------------------------------------------------------------------------

open IO.FS (SystemTime)

/-- A modification time. -/
def MTime := SystemTime

namespace MTime

instance : OfNat MTime (nat_lit 0) := ⟨⟨0,0⟩⟩

instance : BEq MTime := inferInstanceAs (BEq SystemTime)
instance : Repr MTime := inferInstanceAs (Repr SystemTime)

instance : Ord MTime := inferInstanceAs (Ord SystemTime)
instance : LT MTime := ltOfOrd
instance : LE MTime := leOfOrd

instance : NilTrace MTime := ⟨0⟩
instance : MixTrace MTime := ⟨max⟩

end MTime

class GetMTime (α) where
  getMTime : α → IO MTime

export GetMTime (getMTime)
instance [GetMTime α] : ComputeTrace α IO MTime := ⟨getMTime⟩

def getFileMTime (file : FilePath) : IO MTime := do
  (← file.metadata).modified

instance : GetMTime FilePath := ⟨getFileMTime⟩

/-- Check if the info's `MTIme` is at least `depMTime`. -/
def checkIfNewer [GetMTime i] (info : i) (depMTime : MTime) : IO Bool := do
  try (← getMTime info) >= depMTime catch _ => false

--------------------------------------------------------------------------------
-- # Lake Trace (Hash + MTIme)
--------------------------------------------------------------------------------

/-- Trace used for common Lake targets. Combines `Hash` and `MTime`. -/
structure BuildTrace where
  hash : Hash
  mtime : MTime
  deriving Repr

namespace BuildTrace

def withHash (hash : Hash) (self : BuildTrace) : BuildTrace :=
  {self with hash}

def withMTime (mtime : MTime) (self : BuildTrace) : BuildTrace :=
  {self with mtime}

def fromHash (hash : Hash) : BuildTrace :=
  mk hash 0

instance : Coe Hash BuildTrace := ⟨fromHash⟩

def fromMTime (mtime : MTime) : BuildTrace :=
  mk Hash.nil mtime

instance : Coe MTime BuildTrace := ⟨fromMTime⟩

def nil : BuildTrace :=
  mk Hash.nil 0

instance : NilTrace BuildTrace := ⟨nil⟩

def compute [ComputeHash i] [GetMTime i] (info : i) : IO BuildTrace := do
  mk (← computeHash info) (← getMTime info)

instance [ComputeHash i] [GetMTime i] : ComputeTrace i IO BuildTrace := ⟨compute⟩

def mix (t1 t2 : BuildTrace) : BuildTrace :=
  mk (Hash.mix t1.hash t2.hash) (max t1.mtime t2.mtime)

instance : MixTrace BuildTrace := ⟨mix⟩

end BuildTrace
