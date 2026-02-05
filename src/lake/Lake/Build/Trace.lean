/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lean.Data.Json
import Init.Data.Nat.Fold
import Lake.Util.String
public import Init.Data.String.Search
public import Init.Data.String.Extra
import Init.Data.Option.Coe

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

public class CheckExists.{u} (i : Type u) where
  /-- Check whether there already exists an artifact for the given target info. -/
  checkExists : i → BaseIO Bool

export CheckExists (checkExists)

public instance : CheckExists FilePath where
  checkExists := FilePath.pathExists

--------------------------------------------------------------------------------
/-! ## Trace Abstraction -/
--------------------------------------------------------------------------------

public class ComputeTrace (α : Type u) (m : outParam $ Type v → Type w) (τ : Type v) where
  /-- Compute the trace of an object in its preferred monad. -/
  computeTrace : α → m τ

/-- Compute the trace of an object in a supporting monad. -/
@[inline] public def computeTrace [ComputeTrace α m τ] [MonadLiftT m n] (a : α) : n τ :=
  liftM <| ComputeTrace.computeTrace a

public class NilTrace.{u} (α : Type u) where
  /-- The nil trace. Should not unduly clash with a proper trace. -/
  nilTrace : α

export NilTrace (nilTrace)

public instance inhabitedOfNilTrace [NilTrace α] : Inhabited α := ⟨nilTrace⟩

public class MixTrace.{u} (α : Type u) where
  /-- Combine two traces. The result should be dirty if either of the inputs is dirty. -/
  mixTrace : α → α → α

export MixTrace (mixTrace)

section
variable [MixTrace τ] [NilTrace τ]

/- Combine a `List` of traces (left-to-right). -/
public def mixTraceList (traces : List τ) : τ :=
  traces.foldl mixTrace nilTrace

/- Combine an `Array` of traces (left-to-right). -/
public def mixTraceArray (traces : Array τ) : τ :=
  traces.foldl mixTrace nilTrace

variable [ComputeTrace α m τ]

/- Compute the trace of each element of a `List` and combine them (left-to-right). -/
@[inline] public def computeListTrace [MonadLiftT m n] [Monad n] (as : List α) : n τ :=
  as.foldlM (fun ts t => return mixTrace ts (← computeTrace t)) nilTrace

public instance [Monad m] : ComputeTrace (List α) m τ := ⟨computeListTrace⟩

/- Compute the trace of each element of an `Array` and combine them (left-to-right). -/
@[inline] public def computeArrayTrace [MonadLiftT m n] [Monad n] (as : Array α) : n τ :=
  as.foldlM (fun ts t => return mixTrace ts (← computeTrace t)) nilTrace

public instance [Monad m] : ComputeTrace (Array α) m τ := ⟨computeArrayTrace⟩
end

--------------------------------------------------------------------------------
/-! ## Hash Trace -/
--------------------------------------------------------------------------------

/-- A content hash. -/
-- TODO: Use a secure hash rather than the builtin Lean hash function.
public structure Hash where
  val : UInt64
  deriving Repr, DecidableEq

namespace Hash

public instance : Hashable Hash := ⟨Hash.val⟩

public def nil : Hash :=
  mk <| 1723 -- same as Name.anonymous

public instance : NilTrace Hash := ⟨nil⟩

@[inline] public def ofNat (n : Nat) :=
  mk n.toUInt64

/-- Parse a hash from a JSON number. -/
public def ofJsonNumber? (n : JsonNumber) : Except String Hash :=
  if n.exponent = 0 && 0 ≤ n.mantissa then
    if h : n.mantissa.toNat < UInt64.size then
      return ⟨.ofNatLT n.mantissa.toNat h⟩
    else
      throw "number too big"
  else
    throw "number is not a natural"

/-- Parse a hash from a string of hexadecimal digits. Does no validation. -/
public def ofHex (s : String) : Hash :=
  mk <| s.utf8ByteSize.fold (init := 0) fun i h n =>
    let c := s.getUTF8Byte ⟨i⟩ h
    if c ≤ 57 then n*16 + (c - 48).toUInt64
    else if 97 ≤ c then n*16 + (c - 87).toUInt64 -- c - 'a' + 10 = (c - 87)
    else n*16 + (c - 55).toUInt64 -- c - 'A' + 10 = (c - 55)

-- sanity check
example : ofHex "0123456789" = ⟨0x0123456789⟩ ∧
  ofHex "abcdeF" = ⟨0xabcdef⟩ ∧ ofHex "ABCDEF" = ⟨0xABCDEF⟩ := by native_decide

/-- Parse a hash from a 16-digit string of hexadecimal digits. -/
public def ofHex? (s : String) : Option Hash :=
  if s.utf8ByteSize = 16 && isHex s then ofHex s else none

/-- Returns the hash as 16-digit lowercase hex string. -/
public def hex (self : Hash) : String :=
  lpad (String.ofList <| Nat.toDigits 16 self.val.toNat) '0' 16

public def ofDecimal? (s : String) : Option Hash :=
  (inline s.toNat?).map ofNat

@[inline] public def ofString? (s : String) : Option Hash :=
  ofHex? s

public def load? (hashFile : FilePath) : BaseIO (Option Hash) :=
  ofString? <$> IO.FS.readFile hashFile |>.catchExceptions fun _ => pure none

@[inline] public def mix (h1 h2 : Hash) : Hash :=
  mk <| mixHash h1.val h2.val

public instance : MixTrace Hash := ⟨mix⟩

@[inline] public protected def toString (self : Hash) : String :=
  self.hex

public instance : ToString Hash := ⟨Hash.toString⟩

@[inline] public def ofString (str : String) :=
  mix nil <| mk <| hash str -- same as Name.mkSimple

/-- Hash of a line-ending normalized string. -/
@[inline] public def ofText (str : String) :=
  ofString str.crlfToLf

@[inline] public def ofByteArray (bytes : ByteArray) : Hash :=
  ⟨hash bytes⟩

@[inline] public def ofBool (b : Bool) :=
  mk (hash b)

@[inline] public protected def toJson (self : Hash) : Json :=
  toJson self.hex

public instance : ToJson Hash := ⟨Hash.toJson⟩

public protected def fromJson? (json : Json) : Except String Hash := do
  match json with
  | .str s =>
    unless isHex s do
      throw "invalid hash: expected hexadecimal string"
    unless s.utf8ByteSize = 16 do
      throw "invalid hash: expected hexadecimal string of length 16"
    return ofHex s
  | .num n => ofJsonNumber? n |>.mapError (s!"invalid hash: {·}")
  | _ => throw "invalid hash: expected string or number"

public instance : FromJson Hash := ⟨Hash.fromJson?⟩

end Hash

public class ComputeHash (α : Type u) (m : outParam $ Type → Type v)  where
  /-- Compute the hash of an object in its preferred monad. -/
  computeHash : α → m Hash

public instance [ComputeHash α m] : ComputeTrace α m Hash := ⟨ComputeHash.computeHash⟩

/-- Compute the hash of object `a` in a pure context. -/
@[inline] public def pureHash [ComputeHash α Id] (a : α) : Hash :=
  ComputeHash.computeHash a

/-- Compute the hash an object in an supporting monad. -/
@[inline] public def computeHash [ComputeHash α m] [MonadLiftT m n] (a : α) : n Hash :=
  liftM <| ComputeHash.computeHash a

public instance : ComputeHash Bool Id := ⟨Hash.ofBool⟩
public instance : ComputeHash String Id := ⟨Hash.ofString⟩

/--
Compute the hash of a binary file.
Binary files are equivalent only if they are byte identical.
-/
public def computeBinFileHash (file : FilePath) : IO Hash :=
  Hash.ofByteArray <$> IO.FS.readBinFile file

public instance : ComputeHash FilePath IO := ⟨computeBinFileHash⟩

/--
Compute the hash of a text file.
Normalizes `\r\n` sequences to `\n` for cross-platform compatibility.
-/
public def computeTextFileHash (file : FilePath) : IO Hash :=
  Hash.ofText <$> IO.FS.readFile file

/--
A wrapper around `FilePath` that adjusts its `ComputeHash` implementation
to normalize `\r\n` sequences to `\n` for cross-platform compatibility.
-/
public structure TextFilePath where
  path : FilePath

public instance : Coe TextFilePath FilePath := ⟨(·.path)⟩
public instance : ComputeHash TextFilePath IO := ⟨(computeTextFileHash ·)⟩
public instance : ToString TextFilePath := ⟨(·.path.toString)⟩

/-- Compute the hash of a file. If `text := true`, normalize line endings. -/
@[inline] public def computeFileHash (file : FilePath) (text := false) : IO Hash :=
  if text then computeTextFileHash file else computeBinFileHash file

/-- Compute the hash of each element of an array and combine them (left-to-right). -/
@[inline] public def computeArrayHash [ComputeHash α m] [Monad m] (as : Array α) : m Hash :=
  computeArrayTrace as

public instance [ComputeHash α m] [Monad m] : ComputeHash (Array α) m := ⟨computeArrayHash⟩

--------------------------------------------------------------------------------
/-! ## Modification Time (MTime) Trace -/
--------------------------------------------------------------------------------

open IO.FS (SystemTime)

/-- A modification time (e.g., of a file). -/
@[expose] public def MTime := SystemTime

namespace MTime

public instance : OfNat MTime (nat_lit 0) := ⟨⟨0,0⟩⟩

public instance : BEq MTime := inferInstanceAs (BEq SystemTime)
public instance : Repr MTime := inferInstanceAs (Repr SystemTime)

public instance : Ord MTime := inferInstanceAs (Ord SystemTime)
public instance : LT MTime := ltOfOrd
public instance : LE MTime := leOfOrd
public instance : Min MTime := minOfLe
public instance : Max MTime := maxOfLe

public instance : NilTrace MTime := ⟨0⟩
public instance : MixTrace MTime := ⟨max⟩

end MTime

public class GetMTime (α : Type u) where
  /-- Return the modification time of an object. -/
  getMTime : α → IO MTime

export GetMTime (getMTime)
instance [GetMTime α] : ComputeTrace α IO MTime := ⟨getMTime⟩

/-- Return the modification time of a file recorded by the OS. -/
@[inline] public def getFileMTime (file : FilePath) : IO MTime :=
  return (← file.metadata).modified

public instance : GetMTime FilePath := ⟨getFileMTime⟩
public instance : GetMTime TextFilePath := ⟨(getFileMTime ·.path)⟩

/--
Check if `info` is up-to-date using modification time.
That is, check if the info is newer than `self`.
-/
@[specialize] public def MTime.checkUpToDate
  [GetMTime i] (info : i) (self : MTime)
: BaseIO Bool := do
  match (← getMTime info |>.toBaseIO) with
  | .ok mtime => return self < mtime
  | .error _ => return false

--------------------------------------------------------------------------------
/-! ## Lake Build Trace -/
--------------------------------------------------------------------------------

/-- Trace used for common Lake targets. Combines `Hash` and `MTime`. -/
public structure BuildTrace where
  caption : String := ""
  inputs : Array BuildTrace := #[]
  hash : Hash
  mtime : MTime
  deriving Repr

namespace BuildTrace

/-- Sets the caption of the trace. -/
@[inline] public def withCaption (caption : String) (self : BuildTrace) : BuildTrace :=
  {self with caption}

/--
Clear the inputs of the build trace.
This is used to remove unnecessary repetition of trace trees across multiple trace files.
-/
@[inline] public def withoutInputs (self : BuildTrace) : BuildTrace :=
  {self with inputs := #[]}

@[inline] public def ofHash (hash : Hash) (caption := "<hash>") : BuildTrace :=
  {caption, hash, mtime := 0}

public instance : Coe Hash BuildTrace := ⟨ofHash⟩

@[inline] public def ofMTime (mtime : MTime) (caption := "<mtime>") : BuildTrace :=
  {caption, hash := Hash.nil, mtime}

public instance : Coe MTime BuildTrace := ⟨ofMTime⟩

public def nil (caption := "<nil>")  : BuildTrace :=
  {caption, hash := Hash.nil, mtime := 0}

public instance : NilTrace BuildTrace := ⟨nil⟩

@[specialize] public def compute
  [ToString α] [ComputeHash α m] [MonadLiftT m IO] [GetMTime α] (info : α)
: IO BuildTrace :=
  return {
    caption := toString info
    hash := ← computeHash info
    mtime := ← getMTime info
  }

public instance
  [ToString α] [ComputeHash α m] [MonadLiftT m IO] [GetMTime α]
: ComputeTrace α IO BuildTrace := ⟨compute⟩

public def mix (t1 t2 : BuildTrace) : BuildTrace where
  caption := t1.caption
  inputs := t1.inputs.push t2
  hash := Hash.mix t1.hash t2.hash
  mtime := max t1.mtime t2.mtime

public instance : MixTrace BuildTrace := ⟨mix⟩

/--
Check if the info is up-to-date using a hash.
That is, check that info exists and its input hash matches this trace's hash.
-/
@[specialize] public def checkAgainstHash [CheckExists i]
(info : i) (hash : Hash) (self : BuildTrace) : BaseIO Bool :=
  pure (hash == self.hash) <&&> checkExists info

/--
Check if the info is up-to-date using modification time.
That is, check if the info is newer than this input trace's modification time.
-/
@[inline] public def checkAgainstTime
  [GetMTime i] (info : i) (self : BuildTrace)
: BaseIO Bool := do
  self.mtime.checkUpToDate info

end BuildTrace
