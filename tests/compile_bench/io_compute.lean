/-! Mixing basic IO actions and heavy unboxed compute -/

def N : Nat := 12500000 / 2 -- ~50 MB

-- xorshift64* PRNG (same algorithm as Rust version)
@[inline] def xorshift64 (state : UInt64) : UInt64 × UInt64 :=
  let x := state ^^^ (state >>> 12)
  let x := x ^^^ (x <<< 25)
  let x := x ^^^ (x >>> 27)
  (x, x * 0x2545F4914F6CDD1D)

-- Push UInt64 as 8 little-endian bytes
@[inline] def pushLE (ba : ByteArray) (v : UInt64) : ByteArray :=
  let ba := ba.push (v &&& 0xFF).toUInt8
  let ba := ba.push ((v >>> 8) &&& 0xFF).toUInt8
  let ba := ba.push ((v >>> 16) &&& 0xFF).toUInt8
  let ba := ba.push ((v >>> 24) &&& 0xFF).toUInt8
  let ba := ba.push ((v >>> 32) &&& 0xFF).toUInt8
  let ba := ba.push ((v >>> 40) &&& 0xFF).toUInt8
  let ba := ba.push ((v >>> 48) &&& 0xFF).toUInt8
  ba.push ((v >>> 56) &&& 0xFF).toUInt8

-- Read UInt64 from 8 little-endian bytes at offset
@[inline] def readLE (ba : ByteArray) (off : Nat) : UInt64 :=
  (ba.get! off).toUInt64 +
  ((ba.get! (off + 1)).toUInt64 <<< 8) +
  ((ba.get! (off + 2)).toUInt64 <<< 16) +
  ((ba.get! (off + 3)).toUInt64 <<< 24) +
  ((ba.get! (off + 4)).toUInt64 <<< 32) +
  ((ba.get! (off + 5)).toUInt64 <<< 40) +
  ((ba.get! (off + 6)).toUInt64 <<< 48) +
  ((ba.get! (off + 7)).toUInt64 <<< 56)

def timeS {α : Type} (act : IO α) : IO (α × Float) := do
  let t0 ← IO.monoMsNow
  let r ← act
  let t1 ← IO.monoMsNow
  return (r, (t1 - t0).toFloat / 1000.0)

def main : IO Unit := do
  -- Phase 1: Generate & Sort
  let (data, elapsed) ← timeS do
    let mut state : UInt64 := 42
    let mut arr : Array UInt64 := Array.mkEmpty N
    for _ in [:N] do
      let (s, v) := xorshift64 state
      state := s
      arr := arr.push v
    return arr.qsortOrd
  IO.println s!"measurement: generate_sort {elapsed} s"

  let (_, file) ← IO.FS.createTempFile
  -- Phase 2: Write
  let (_, elapsed) ← timeS do
    let mut ba := ByteArray.emptyWithCapacity (N * 8)
    for i in [:data.size] do
      ba := pushLE ba data[i]!
    IO.FS.writeBinFile file ba
  IO.println s!"measurement: write {elapsed} s"

  -- Phase 3: Read
  let (data, elapsed) ← timeS do
    let ba ← IO.FS.readBinFile file
    let mut arr : Array UInt64 := Array.mkEmpty N
    for i in [:N] do
      arr := arr.push (readLE ba (i * 8))
    return arr
  IO.println s!"measurement: read {elapsed} s"

  -- Phase 4: Fisher-Yates shuffle
  let (_, elapsed) ← timeS do
    let mut arr := data
    let mut state : UInt64 := 42
    for i' in [:N - 1] do
      let i := N - 1 - i'
      let (s, v) := xorshift64 state
      state := s
      let j := (v % (i + 1).toUInt64).toNat
      arr := arr.swapIfInBounds i j
    return arr
  IO.println s!"measurement: shuffle {elapsed} s"

