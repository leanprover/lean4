import Lean.CompactedRegion

open Lean

/-!
Regression test for #3826: reading a file whose mapping is still alive must reuse that mapping
instead of falling back to `malloc` + `read` + pointer fixup, and the mapping must stay valid
until every region using it has been freed. Sharing is sound because nothing writes to a `v2`
mapping after loading, which requires `v2` files not to contain `IO.Ref`s or `IO.Promise`s.
-/
unsafe def main : IO UInt32 := do
  -- Mappings are only shared on POSIX.
  if System.Platform.isWindows then return 0
  let file : System.FilePath := "./_tmp_shared_mapping.olean"
  let payload : Array Nat := (Array.range 256).map (· * 7)
  let _ ← CompactedRegion.save file `SharedMapping payload #[] none

  let (loaded1, r1) ← CompactedRegion.read (α := Array Nat) file #[]
  -- Nothing to share if the first load did not get its `base_addr`.
  unless r1.isMemoryMapped do return 0

  -- Second load of the same file while `r1` is alive: shares `r1`'s mapping.
  let (loaded2, r2) ← CompactedRegion.read (α := Array Nat) file #[]
  unless r2.isMemoryMapped do
    throw <| IO.userError "second load did not reuse the existing mapping"
  unless loaded2 = payload do
    throw <| IO.userError "shared load did not round-trip"

  -- Freeing one user must not unmap the mapping the other still uses.
  r1.free
  unless loaded2 = payload do
    throw <| IO.userError "data changed after freeing the other user"
  r2.free

  -- Rewriting the file replaces it with a new one (`save` renames into place), which must not be
  -- served from the old mapping even though both have the same `base_addr`.
  let (_, r3) ← CompactedRegion.read (α := Array Nat) file #[]
  let payload' : Array Nat := (Array.range 256).map (· * 11)
  let _ ← CompactedRegion.save file `SharedMapping payload' #[] none
  let (loaded4, _r4) ← CompactedRegion.read (α := Array Nat) file #[]
  unless loaded4 = payload' do
    throw <| IO.userError "rewritten file was served from the old mapping"
  r3.free

  -- `IO.Ref`s and `IO.Promise`s are written to after loading, so they cannot be saved in the
  -- shareable `v2` format.
  let ref ← IO.mkRef (0 : Nat)
  if let .ok _ ← (CompactedRegion.save file `SharedMapping ref #[] none).toBaseIO then
    throw <| IO.userError "saved an `IO.Ref` without `allowClosures`"
  let promise ← IO.Promise.new (α := Nat)
  if let .ok _ ← (CompactedRegion.save file `SharedMapping promise #[] none).toBaseIO then
    throw <| IO.userError "saved an `IO.Promise` without `allowClosures`"

  IO.FS.removeFile file
  return 0
