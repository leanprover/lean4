/-!
Tests `ByteArray.ugetUInt32LE` and `ByteArray.usetUInt32LE`: unaligned offsets, and updates of shared
arrays, including in a loop whose first update must copy.
-/

def bytes : ByteArray := ⟨#[0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88]⟩

def getSpec (a : ByteArray) (i : Nat) : UInt32 :=
  (a.get! i).toUInt32 ||| (a.get! (i+1)).toUInt32 <<< 8 |||
  (a.get! (i+2)).toUInt32 <<< 16 ||| (a.get! (i+3)).toUInt32 <<< 24

@[noinline] def get (a : @& ByteArray) (i : Nat) : UInt32 :=
  if h : i.toUSize.toNat + 4 ≤ a.size then a.ugetUInt32LE i.toUSize h else 0

@[noinline] def set (a : ByteArray) (i : Nat) (v : UInt32) : ByteArray :=
  if h : i.toUSize.toNat + 4 ≤ a.size then a.usetUInt32LE i.toUSize v h else a

/-- Writes `v + k` at byte offset `off + 4 * k` for `k < n`. -/
@[noinline] def fill (a : ByteArray) (off n : Nat) (v : UInt32) : ByteArray := Id.run do
  let mut a := a
  for k in [0:n] do
    let i := off + 4 * k
    if h : i.toUSize.toNat + 4 ≤ a.size then
      a := a.usetUInt32LE i.toUSize (v + k.toUInt32) h
  return a

def hex (v : UInt32) : String := String.ofList (Nat.toDigits 16 v.toNat)

def main : IO Unit := do
  for i in [0:5] do
    IO.println s!"get {i}: {hex (get bytes i)} {get bytes i == getSpec bytes i}"
  -- `bytes` is shared, so this must copy
  let b := set bytes 1 0xaabbccdd
  IO.println s!"set: {b} {bytes}"
  -- shared on entry: the first update copies, the remaining ones update the copy in place
  let z := ByteArray.mk (Array.replicate 18 0)
  let f := fill z 1 4 0x01020304
  IO.println s!"fill shared: {f} {z}"
  IO.println s!"read back: {(List.range 4).all fun k => getSpec f (1 + 4 * k) == 0x01020304 + k.toUInt32}"
  let e := fill (ByteArray.mk (Array.replicate 18 0)) 2 4 0xfffffffe
  IO.println s!"fill exclusive: {e}"
