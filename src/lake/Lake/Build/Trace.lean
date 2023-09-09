/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/

open System
namespace Lake

--------------------------------------------------------------------------------
/-! # Utilities -/
--------------------------------------------------------------------------------

class CheckExists.{u} (i : Type u) where
  /-- Check whether there already exists an artifact for the given target info. -/
  checkExists : i → BaseIO Bool

export CheckExists (checkExists)

instance : CheckExists FilePath where
  checkExists := FilePath.pathExists

--------------------------------------------------------------------------------
/-! # Trace Abstraction -/
--------------------------------------------------------------------------------

class ComputeTrace.{u,v,w} (i : Type u) (m : outParam $ Type v → Type w) (t : Type v) where
  /--  Compute the trace of some target info using information from the monadic context. -/
  computeTrace : i → m t

@[inline] def computeTrace [ComputeTrace i m t] [MonadLiftT m n] (info : i) : n t :=
  liftM <| ComputeTrace.computeTrace info

class NilTrace.{u} (t : Type u) where
  /-- The nil trace. Should not unduly clash with a proper trace. -/
  nilTrace : t

export NilTrace (nilTrace)

instance [NilTrace t] : Inhabited t := ⟨nilTrace⟩

class MixTrace.{u} (t : Type u) where
  /-- Combine two traces. The result should be dirty if either of the inputs is dirty. -/
  mixTrace : t → t → t

export MixTrace (mixTrace)

section
variable [MixTrace t] [NilTrace t]

def mixTraceList (traces : List t) : t :=
  traces.foldl mixTrace nilTrace

def mixTraceArray (traces : Array t) : t :=
  traces.foldl mixTrace nilTrace

variable [ComputeTrace i m t]

@[specialize] def computeListTrace [MonadLiftT m n] [Monad n] (artifacts : List i) : n t :=
  artifacts.foldlM (fun ts t => return mixTrace ts (← computeTrace t)) nilTrace

instance [Monad m] : ComputeTrace (List i) m t := ⟨computeListTrace⟩

@[specialize] def computeArrayTrace [MonadLiftT m n] [Monad n] (artifacts : Array i) : n t :=
  artifacts.foldlM (fun ts t => return mixTrace ts (← computeTrace t)) nilTrace

instance [Monad m] : ComputeTrace (Array i) m t := ⟨computeArrayTrace⟩
end

--------------------------------------------------------------------------------
/-! # Hash Trace -/
--------------------------------------------------------------------------------

/--
A content hash.
TODO: Use a secure hash rather than the builtin Lean hash function.
-/
structure Hash where
  val : UInt64
  deriving BEq, DecidableEq, Repr

namespace Hash

@[inline] def ofNat (n : Nat) :=
  mk n.toUInt64

def load? (hashFile : FilePath) : BaseIO (Option Hash) :=
  (·.toNat?.map ofNat) <$> IO.FS.readFile hashFile |>.catchExceptions fun _ => pure none

def nil : Hash :=
  mk <| 1723 -- same as Name.anonymous

instance : NilTrace Hash := ⟨nil⟩

@[inline] def mix (h1 h2 : Hash) : Hash :=
  mk <| mixHash h1.val h2.val

instance : MixTrace Hash := ⟨mix⟩

@[inline] protected def toString (self : Hash) : String :=
  toString self.val

instance : ToString Hash := ⟨Hash.toString⟩

@[inline] def ofString (str : String) :=
  mix nil <| mk <| hash str -- same as Name.mkSimple

@[inline] def ofByteArray (bytes : ByteArray) : Hash :=
  ⟨hash bytes⟩

end Hash

class ComputeHash (α : Type u) (m : outParam $ Type → Type v)  where
  computeHash : α → m Hash

instance [ComputeHash α m] : ComputeTrace α m Hash := ⟨ComputeHash.computeHash⟩

@[inline] def pureHash [ComputeHash α Id] (a : α) : Hash :=
  ComputeHash.computeHash a

@[inline] def computeHash [ComputeHash α m] [MonadLiftT m n] (a : α) : n Hash :=
  liftM <| ComputeHash.computeHash a

instance : ComputeHash String Id := ⟨Hash.ofString⟩

def computeFileHash (file : FilePath) : IO Hash :=
  Hash.ofByteArray <$> IO.FS.readBinFile file

instance : ComputeHash FilePath IO := ⟨computeFileHash⟩

/-- This is the same as `String.replace text "\r\n" "\n"`, but more efficient. -/
@[inline] partial def crlf2lf (text : String) : String :=
  go "" 0 0
where
  go (acc : String) (accStop pos : String.Pos) : String :=
    if h : text.atEnd pos then
      -- note: if accStop = 0 then acc is empty
      if accStop = 0 then text else acc ++ text.extract accStop pos
    else
      let c := text.get' pos h
      let pos' := text.next' pos h
      if c == '\r' && text.get pos' == '\n' then
        let acc := acc ++ text.extract accStop pos
        go acc pos' (text.next pos')
      else
        go acc accStop pos'

def computeTextFileHash (file : FilePath) : IO Hash := do
  let text ← IO.FS.readFile file
  let text := crlf2lf text
  return Hash.ofString text

/--
  A wrapper around `FilePath` that adjusts its `ComputeHash` implementation
  to normalize `\r\n` sequences to `\n` for cross-platform compatibility. -/
structure TextFilePath where
  path : FilePath

instance : Coe TextFilePath FilePath := ⟨(·.path)⟩

instance : ComputeHash TextFilePath IO where
  computeHash file := computeTextFileHash file

@[specialize] def computeArrayHash [ComputeHash α m] [Monad m] (xs : Array α) : m Hash :=
  xs.foldlM (fun h a => return h.mix (← computeHash a)) .nil

instance [ComputeHash α m] [Monad m] : ComputeHash (Array α) m := ⟨computeArrayHash⟩

--------------------------------------------------------------------------------
/-! # Modification Time (MTime) Trace -/
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
instance : Min MTime := minOfLe
instance : Max MTime := maxOfLe

instance : NilTrace MTime := ⟨0⟩
instance : MixTrace MTime := ⟨max⟩

end MTime

class GetMTime (α) where
  getMTime : α → IO MTime

export GetMTime (getMTime)
instance [GetMTime α] : ComputeTrace α IO MTime := ⟨getMTime⟩

@[inline] def getFileMTime (file : FilePath) : IO MTime :=
  return (← file.metadata).modified

instance : GetMTime FilePath := ⟨getFileMTime⟩
instance : GetMTime TextFilePath := ⟨(getFileMTime ·.path)⟩

--------------------------------------------------------------------------------
/-! # Lake Build Trace (Hash + MTIme) -/
--------------------------------------------------------------------------------

/-- Trace used for common Lake targets. Combines `Hash` and `MTime`. -/
structure BuildTrace where
  hash : Hash
  mtime : MTime
  deriving Repr

namespace BuildTrace

@[inline] def ofHash (hash : Hash) : BuildTrace :=
  mk hash 0

instance : Coe Hash BuildTrace := ⟨ofHash⟩

@[inline] def ofMTime (mtime : MTime) : BuildTrace :=
  mk Hash.nil mtime

instance : Coe MTime BuildTrace := ⟨ofMTime⟩

def nil : BuildTrace :=
  mk Hash.nil 0

instance : NilTrace BuildTrace := ⟨nil⟩

@[specialize] def compute [ComputeHash i m] [MonadLiftT m IO] [GetMTime i] (info : i) : IO BuildTrace :=
  return mk (← computeHash info) (← getMTime info)

instance [ComputeHash i m] [MonadLiftT m IO] [GetMTime i] : ComputeTrace i IO BuildTrace := ⟨compute⟩

def mix (t1 t2 : BuildTrace) : BuildTrace :=
  mk (Hash.mix t1.hash t2.hash) (max t1.mtime t2.mtime)

instance : MixTrace BuildTrace := ⟨mix⟩

/--
Check if the info is up-to-date using a hash.
That is, check that info exists and its input hash matches this trace's hash.
-/
@[inline] def checkAgainstHash [CheckExists i]
(info : i) (hash : Hash) (self : BuildTrace) : BaseIO Bool :=
  pure (hash == self.hash) <&&> checkExists info

/--
Check if the info is up-to-date using modification time.
That is, check if the info is newer than this input trace's modification time.
-/
@[inline] def checkAgainstTime [GetMTime i]
(info : i) (self : BuildTrace) : BaseIO Bool :=
  EIO.catchExceptions (h := fun _ => pure false) do
    return self.mtime < (← getMTime info)

/--
Check if the info is up-to-date using a trace file.
If the file exists, match its hash to this trace's hash.
If not, check if the info is newer than this trace's modification time.
-/
@[inline] def checkAgainstFile [CheckExists i] [GetMTime i]
(info : i) (traceFile : FilePath) (self : BuildTrace) : BaseIO Bool := do
  if let some hash ← Hash.load? traceFile then
    self.checkAgainstHash info hash
  else
    self.checkAgainstTime info

@[inline] def writeToFile (traceFile : FilePath) (self : BuildTrace) : IO PUnit :=
  IO.FS.writeFile traceFile self.hash.toString

end BuildTrace
