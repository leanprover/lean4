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

def computeTrace [ComputeTrace i m t] [MonadLiftT m n] (info : i) : n t :=
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

def mixTraceM [MixTrace t] [Pure m] (t1 t2 : t) : m t :=
  pure <| mixTrace t1 t2

section
variable [MixTrace t] [NilTrace t]

def mixTraceList (traces : List t) : t :=
  traces.foldl mixTrace nilTrace

def mixTraceArray (traces : Array t) : t :=
  traces.foldl mixTrace nilTrace

variable [ComputeTrace i m t]

def computeListTrace [MonadLiftT m n] [Monad n] (artifacts : List i) : n t :=
  mixTraceList <$> artifacts.mapM computeTrace

instance [Monad m] : ComputeTrace (List i) m t := ⟨computeListTrace⟩

def computeArrayTrace [MonadLiftT m n] [Monad n] (artifacts : Array i) : n t :=
  mixTraceArray <$> artifacts.mapM computeTrace

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

def ofNat (n : Nat) :=
  mk n.toUInt64

def loadFromFile (hashFile : FilePath) : IO (Option Hash) :=
  return (← IO.FS.readFile hashFile).toNat?.map ofNat

def nil : Hash :=
  mk <| 1723 -- same as Name.anonymous

instance : NilTrace Hash := ⟨nil⟩

def mix (h1 h2 : Hash) : Hash :=
  mk <| mixHash h1.val h2.val

instance : MixTrace Hash := ⟨mix⟩

protected def toString (self : Hash) : String :=
  toString self.val

instance : ToString Hash := ⟨Hash.toString⟩

def ofString (str : String) :=
  mix nil <| mk <| hash str -- same as Name.mkSimple

def ofByteArray (bytes : ByteArray) : Hash :=
  ⟨hash bytes⟩

end Hash

class ComputeHash (α : Type u) (m : outParam $ Type → Type v)  where
  computeHash : α → m Hash

instance [ComputeHash α m] : ComputeTrace α m Hash := ⟨ComputeHash.computeHash⟩

def pureHash [ComputeHash α Id] (a : α) : Hash :=
  ComputeHash.computeHash a

def computeHash [ComputeHash α m] [MonadLiftT m n] (a : α) : n Hash :=
  liftM <| ComputeHash.computeHash a

instance : ComputeHash String Id := ⟨Hash.ofString⟩

def computeFileHash (file : FilePath) : IO Hash :=
  Hash.ofByteArray <$> IO.FS.readBinFile file

instance : ComputeHash FilePath IO := ⟨computeFileHash⟩

/--
  A wrapper around `FilePath` that adjusts its `ComputeHash` implementation
  to normalize `\r\n` sequences to `\n` for cross-platform compatibility. -/
structure TextFilePath where
  path : FilePath

/-- This is the same as `String.replace text "\r\n" "\n"`, but more efficient. -/
partial def crlf2lf (text : String) : String :=
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

instance : ComputeHash TextFilePath IO where
  computeHash file := do
    let text ← IO.FS.readFile file.path
    let text := crlf2lf text
    return Hash.ofString text

instance [ComputeHash α m] [Monad m] : ComputeHash (Array α) m where
  computeHash ar := ar.foldlM (fun b a => Hash.mix b <$> computeHash a) Hash.nil

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

def getFileMTime (file : FilePath) : IO MTime :=
  return (← file.metadata).modified

instance : GetMTime FilePath := ⟨getFileMTime⟩
instance : GetMTime TextFilePath := ⟨(getFileMTime ·.path)⟩

/-- Check if the info's `MTIme` is at least `depMTime`. -/
def checkIfNewer [GetMTime i] (info : i) (depMTime : MTime) : BaseIO Bool :=
  (do pure ((← getMTime info) >= depMTime : Bool)).catchExceptions fun _ => pure false

--------------------------------------------------------------------------------
/-! # Lake Build Trace (Hash + MTIme) -/
--------------------------------------------------------------------------------

/-- Trace used for common Lake targets. Combines `Hash` and `MTime`. -/
structure BuildTrace where
  hash : Hash
  mtime : MTime
  deriving Repr

namespace BuildTrace

def withHash (hash : Hash) (self : BuildTrace) : BuildTrace :=
  {self with hash}

def withoutHash (self : BuildTrace) : BuildTrace :=
  {self with hash := Hash.nil}

def withMTime (mtime : MTime) (self : BuildTrace) : BuildTrace :=
  {self with mtime}

def withoutMTime (self : BuildTrace) : BuildTrace :=
  {self with mtime := 0}

def fromHash (hash : Hash) : BuildTrace :=
  mk hash 0

instance : Coe Hash BuildTrace := ⟨fromHash⟩

def fromMTime (mtime : MTime) : BuildTrace :=
  mk Hash.nil mtime

instance : Coe MTime BuildTrace := ⟨fromMTime⟩

def nil : BuildTrace :=
  mk Hash.nil 0

instance : NilTrace BuildTrace := ⟨nil⟩

def compute [ComputeHash i m] [MonadLiftT m IO] [GetMTime i] (info : i) : IO BuildTrace :=
  return mk (← computeHash info) (← getMTime info)

instance [ComputeHash i m] [MonadLiftT m IO] [GetMTime i] : ComputeTrace i IO BuildTrace := ⟨compute⟩

def mix (t1 t2 : BuildTrace) : BuildTrace :=
  mk (Hash.mix t1.hash t2.hash) (max t1.mtime t2.mtime)

instance : MixTrace BuildTrace := ⟨mix⟩

/--
Check the build trace against the given target info and hash
to see if the target is up-to-date.
-/
def checkAgainstHash [CheckExists i]
(info : i) (hash : Hash) (self : BuildTrace) : BaseIO Bool :=
  pure (hash == self.hash) <&&> checkExists info

/--
Check the build trace against the given target info and its modification time
to see if the target is up-to-date.
-/
def checkAgainstTime [CheckExists i] [GetMTime i]
(info : i) (self : BuildTrace) : BaseIO Bool :=
  checkIfNewer info self.mtime

/--
Check the build trace against the given target info and its trace file
to see if the target is up-to-date.
-/
def checkAgainstFile [CheckExists i] [GetMTime i]
(info : i) (traceFile : FilePath) (self : BuildTrace) : BaseIO Bool := do
  let act : IO _ := do
    if let some hash ← Hash.loadFromFile traceFile then
      self.checkAgainstHash info hash
    else
      return self.mtime < (← getMTime info)
  act.catchExceptions fun _ => pure false

def writeToFile (traceFile : FilePath) (self : BuildTrace) : IO PUnit :=
  IO.FS.writeFile traceFile self.hash.toString

end BuildTrace
