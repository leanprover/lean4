import Lean.CompactedRegion

open Lean

/-!
Tests that `CompactedRegion.read` reports an error for a truncated file and for a closure offset
that points outside the compacted data.
-/

/-- `sizeof(olean_header)` in `src/library/module.cpp`. -/
def headerSize : Nat := 88

def getUInt64LE (bs : ByteArray) (pos : Nat) : Nat := Id.run do
  let mut r := 0
  for i in [0:8] do
    r := r + bs[pos + i]!.toNat <<< (8 * i)
  return r

def setUInt64LE (bs : ByteArray) (pos : Nat) (v : Nat) : ByteArray := Id.run do
  let mut bs := bs
  for i in [0:8] do
    bs := bs.set! (pos + i) (v >>> (8 * i)).toUInt8
  return bs

unsafe def tryRead (file : System.FilePath) : IO (Option String) := do
  try
    let (_, region) ← CompactedRegion.read (α := Nat → String) file #[]
    -- Windows does not allow overwriting a file that is still mapped.
    region.free
    return none
  catch e =>
    return some (toString e)

unsafe def main : IO Unit := do
  let file : System.FilePath := "./_tmp_olean_truncated.olean"
  let captured := "hello"
  let f : Nat → String := fun n => s!"{captured} {n}"
  let _ ← CompactedRegion.save file `test f #[] none true
  let bytes ← IO.FS.readBinFile file

  let mut accepted := #[]
  for len in [0:bytes.size] do
    IO.FS.writeBinFile file (bytes.extract 0 len)
    if (← tryRead file).isNone then
      accepted := accepted.push len
  IO.println s!"truncated lengths accepted: {accepted}"

  let dataSize := getUInt64LE bytes headerSize
  let firstOffsetPos := headerSize + 8 + dataSize + 4
  for (descr, off) in [("last word", dataSize - 8), ("straddles end", dataSize - 4),
      ("at end", dataSize), ("max", 2^64 - 1)] do
    IO.FS.writeBinFile file (setUInt64LE bytes firstOffsetPos off)
    IO.println s!"closure offset {descr}: {← tryRead file}"

  IO.FS.writeBinFile file bytes
  IO.println s!"intact: {← tryRead file}"
  IO.FS.removeFile file
