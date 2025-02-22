/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Util.IO
import Lean.Data.Json

/-! # Lake Traces

This module defines Lake traces and associated utilities.
Traces are used to determine whether a Lake build artifact is *dirty*
(needs to be rebuilt) or is already *up-to-date*.
The primary type is `Lake.BuildTrace`.
-/

open System Lean

namespace Lake

--------------------------------------------------------------------------------
/-! ## Utilities -/
--------------------------------------------------------------------------------

class CheckExists.{u} (i : Type u) where
  /-- Check whether there already exists an artifact for the given target info. -/
  checkExists : i → BaseIO Bool

export CheckExists (checkExists)

instance : CheckExists FilePath where
  checkExists := FilePath.pathExists

--------------------------------------------------------------------------------
/-! ## Trace Abstraction -/
--------------------------------------------------------------------------------

class ComputeTrace (α : Type u) (m : outParam $ Type v → Type w) (τ : Type v) where
  /-- Compute the trace of an object in its preferred monad. -/
  computeTrace : α → m τ

/-- Compute the trace of an object in a supporting monad. -/
@[inline] def computeTrace [ComputeTrace α m τ] [MonadLiftT m n] (a : α) : n τ :=
  liftM <| ComputeTrace.computeTrace a

class NilTrace.{u} (α : Type u) where
  /-- The nil trace. Should not unduly clash with a proper trace. -/
  nilTrace : α

export NilTrace (nilTrace)

instance inhabitedOfNilTrace [NilTrace α] : Inhabited α := ⟨nilTrace⟩

class MixTrace.{u} (α : Type u) where
  /-- Combine two traces. The result should be dirty if either of the inputs is dirty. -/
  mixTrace : α → α → α

export MixTrace (mixTrace)

section
variable [MixTrace τ] [NilTrace τ]

/- Combine a `List` of traces (left-to-right). -/
def mixTraceList (traces : List τ) : τ :=
  traces.foldl mixTrace nilTrace

/- Combine an `Array` of traces (left-to-right). -/
def mixTraceArray (traces : Array τ) : τ :=
  traces.foldl mixTrace nilTrace

variable [ComputeTrace α m τ]

/- Compute the trace of each element of a `List` and combine them (left-to-right). -/
@[inline] def computeListTrace [MonadLiftT m n] [Monad n] (as : List α) : n τ :=
  as.foldlM (fun ts t => return mixTrace ts (← computeTrace t)) nilTrace

instance [Monad m] : ComputeTrace (List α) m τ := ⟨computeListTrace⟩

/- Compute the trace of each element of an `Array` and combine them (left-to-right). -/
@[inline] def computeArrayTrace [MonadLiftT m n] [Monad n] (as : Array α) : n τ :=
  as.foldlM (fun ts t => return mixTrace ts (← computeTrace t)) nilTrace

instance [Monad m] : ComputeTrace (Array α) m τ := ⟨computeArrayTrace⟩
end

--------------------------------------------------------------------------------
/-! ## Hash Trace -/
--------------------------------------------------------------------------------

/-- A content hash. -/
-- TODO: Use a secure hash rather than the builtin Lean hash function.
structure Hash where
  val : UInt64
  deriving BEq, DecidableEq, Repr

namespace Hash

@[inline] def ofNat (n : Nat) :=
  mk n.toUInt64

def ofString? (s : String) : Option Hash :=
  (inline s.toNat?).map ofNat

def load? (hashFile : FilePath) : BaseIO (Option Hash) :=
  ofString? <$> IO.FS.readFile hashFile |>.catchExceptions fun _ => pure none

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

@[inline] def ofBool (b : Bool) :=
  mk (hash b)

@[inline] protected def toJson (self : Hash) : Json :=
  toJson self.val

instance : ToJson Hash := ⟨Hash.toJson⟩

@[inline] protected def fromJson? (json : Json) : Except String Hash :=
  (⟨·⟩) <$> fromJson? json

instance : FromJson Hash := ⟨Hash.fromJson?⟩

end Hash

class ComputeHash (α : Type u) (m : outParam $ Type → Type v)  where
  /-- Compute the hash of an object in its preferred monad. -/
  computeHash : α → m Hash

instance [ComputeHash α m] : ComputeTrace α m Hash := ⟨ComputeHash.computeHash⟩

/-- Compute the hash of object `a` in a pure context. -/
@[inline] def pureHash [ComputeHash α Id] (a : α) : Hash :=
  ComputeHash.computeHash a

/-- Compute the hash an object in an supporting monad. -/
@[inline] def computeHash [ComputeHash α m] [MonadLiftT m n] (a : α) : n Hash :=
  liftM <| ComputeHash.computeHash a

instance : ComputeHash Bool Id := ⟨Hash.ofBool⟩
instance : ComputeHash String Id := ⟨Hash.ofString⟩

/--
Compute the hash of a binary file.
Binary files are equivalent only if they are byte identical.
-/
def computeBinFileHash (file : FilePath) : IO Hash :=
  Hash.ofByteArray <$> IO.FS.readBinFile file

instance : ComputeHash FilePath IO := ⟨computeBinFileHash⟩

/--
Compute the hash of a text file.
Normalizes `\r\n` sequences to `\n` for cross-platform compatibility.
-/
def computeTextFileHash (file : FilePath) : IO Hash := do
  let text ← IO.FS.readFile file
  let text := text.crlfToLf
  return Hash.ofString text

/--
A wrapper around `FilePath` that adjusts its `ComputeHash` implementation
to normalize `\r\n` sequences to `\n` for cross-platform compatibility.
-/
structure TextFilePath where
  path : FilePath

instance : Coe TextFilePath FilePath := ⟨(·.path)⟩
instance : ComputeHash TextFilePath IO := ⟨(computeTextFileHash ·)⟩

/-- Compute the hash of a file. If `text := true`, normalize line endings. -/
@[inline] def computeFileHash (file : FilePath) (text := false) : IO Hash :=
  if text then computeTextFileHash file else computeBinFileHash file

/-- Compute the hash of each element of an array and combine them (left-to-right). -/
@[inline] def computeArrayHash [ComputeHash α m] [Monad m] (as : Array α) : m Hash :=
  computeArrayTrace as

instance [ComputeHash α m] [Monad m] : ComputeHash (Array α) m := ⟨computeArrayHash⟩

--------------------------------------------------------------------------------
/-! ## Modification Time (MTime) Trace -/
--------------------------------------------------------------------------------

open IO.FS (SystemTime)

/-- A modification time (e.g., of a file). -/
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

class GetMTime (α : Type u) where
  /-- Return the modification time of an object. -/
  getMTime : α → IO MTime

export GetMTime (getMTime)
instance [GetMTime α] : ComputeTrace α IO MTime := ⟨getMTime⟩

/-- Return the modification time of a file recorded by the OS. -/
@[inline] def getFileMTime (file : FilePath) : IO MTime :=
  return (← file.metadata).modified

instance : GetMTime FilePath := ⟨getFileMTime⟩
instance : GetMTime TextFilePath := ⟨(getFileMTime ·.path)⟩

/--
Check if `info` is up-to-date using modification time.
That is, check if the info is newer than `self`.
-/
@[specialize] def MTime.checkUpToDate
  [GetMTime i] (info : i) (self : MTime)
: BaseIO Bool := do
  match (← getMTime info |>.toBaseIO) with
  | .ok mtime => return self < mtime
  | .error _ => return false

--------------------------------------------------------------------------------
/-! ## Lake Build Trace -/
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

@[specialize] def compute [ComputeHash α m] [MonadLiftT m IO] [GetMTime α] (info : α) : IO BuildTrace :=
  return mk (← computeHash info) (← getMTime info)

instance [ComputeHash α m] [MonadLiftT m IO] [GetMTime α] : ComputeTrace α IO BuildTrace := ⟨compute⟩

def mix (t1 t2 : BuildTrace) : BuildTrace :=
  mk (Hash.mix t1.hash t2.hash) (max t1.mtime t2.mtime)

instance : MixTrace BuildTrace := ⟨mix⟩

/--
Check if the info is up-to-date using a hash.
That is, check that info exists and its input hash matches this trace's hash.
-/
@[specialize] def checkAgainstHash [CheckExists i]
(info : i) (hash : Hash) (self : BuildTrace) : BaseIO Bool :=
  pure (hash == self.hash) <&&> checkExists info

/--
Check if the info is up-to-date using modification time.
That is, check if the info is newer than this input trace's modification time.
-/
@[inline] def checkAgainstTime
  [GetMTime i] (info : i) (self : BuildTrace)
: BaseIO Bool := do
  self.mtime.checkUpToDate info

/--
Check if the info is up-to-date using a trace file.
If the file exists, match its hash to this trace's hash.
If not, check if the info is newer than this trace's modification time.

**Deprecated:** Should not be done manually,
but as part of `buildUnlessUpToDate`.
-/
@[deprecated "Should not be done manually, but as part of `buildUnlessUpToDate`."
  (since := "2024-06-14"), specialize]
def checkAgainstFile
  [CheckExists i] [GetMTime i]
  (info : i) (traceFile : FilePath) (self : BuildTrace)
: BaseIO Bool := do
  if let some hash ← Hash.load? traceFile then
    self.checkAgainstHash info hash
  else
    self.checkAgainstTime info

/--
Write trace to a file.

**Deprecated:** Should not be done manually,
but as part of `buildUnlessUpToDate`.
-/
@[deprecated "Should not be done manually, but as part of `buildUnlessUpToDate`." (since := "2024-06-14")]
def writeToFile (traceFile : FilePath) (self : BuildTrace) : IO PUnit := do
  createParentDirs traceFile
  IO.FS.writeFile traceFile self.hash.toString

end BuildTrace
