/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/

open System
namespace Lake

-- # Hash Traces

structure Hash where
  val : UInt64
  deriving BEq, DecidableEq

namespace Hash

def nil : Hash :=
  mk <| 1723 -- same as Name.anonymous

instance : Inhabited Hash := ⟨nil⟩

def compute (str : String) :=
  mk <| mixHash 1723 (hash str) -- same as Name.mkSimple

def mix (h1 h2 : Hash) : Hash :=
  mk <| mixHash h1.val h2.val

def mixList (hashes : List Hash) : Hash :=
  hashes.foldl mix nil

def mixArray (hashes : Array Hash) : Hash :=
  hashes.foldl mix nil

protected def toString (self : Hash) : String :=
  toString self.val

instance : ToString Hash := ⟨Hash.toString⟩

end Hash

class ComputeHash (α) where
  computeHash : α → IO Hash

export ComputeHash (computeHash)

def getFileHash (file : FilePath) : IO Hash :=
  Hash.compute <$> IO.FS.readFile file

instance : ComputeHash FilePath := ⟨getFileHash⟩
instance : ComputeHash String := ⟨pure ∘ Hash.compute⟩

-- # Modification Time Traces

open IO.FS (SystemTime)

def MTime := SystemTime

namespace MTime

instance : Inhabited MTime := ⟨⟨0,0⟩⟩
instance : OfNat MTime (nat_lit 0) := ⟨⟨0,0⟩⟩
instance : BEq MTime := inferInstanceAs (BEq SystemTime)
instance : Repr MTime := inferInstanceAs (Repr SystemTime)
instance : Ord MTime := inferInstanceAs (Ord SystemTime)
instance : LT MTime := ltOfOrd
instance : LE MTime := leOfOrd

def listMax (mtimes : List MTime) := mtimes.foldl max 0
def arrayMax (mtimes : Array MTime) := mtimes.foldl max 0

end MTime

class GetMTime (α) where
  getMTime : α → IO MTime

export GetMTime (getMTime)

def getFileMTime (file : FilePath) : IO MTime := do
  (← file.metadata).modified

instance : GetMTime FilePath := ⟨getFileMTime⟩

/-- Check if the artifact's `MTIme` is at least `depMTime`. -/
def checkIfNewer [GetMTime a] (artifact : a) (depMTime : MTime) : IO Bool := do
  try (← getMTime artifact) >= depMTime catch _ => false

-- # Combined Trace

structure LakeTrace where
  hash : Hash
  mtime : MTime

namespace LakeTrace

def nil : LakeTrace :=
  mk Hash.nil 0

instance : Inhabited LakeTrace := ⟨nil⟩

def compute [ComputeHash a] [GetMTime a] (artifact : a) : IO LakeTrace := do
  mk (← computeHash artifact) (← getMTime artifact)

def fromHash (hash : Hash) : LakeTrace :=
  mk hash 0

def fromMTime (mtime : MTime) : LakeTrace :=
  mk Hash.nil mtime

def mix (t1 t2 : LakeTrace) : LakeTrace :=
  mk (Hash.mix t1.hash t2.hash) (max t1.mtime t2.mtime)

def mixList (traces : List LakeTrace) : LakeTrace :=
  traces.foldl mix nil

def mixArray (traces : Array LakeTrace) : LakeTrace :=
  traces.foldl mix nil

end LakeTrace
