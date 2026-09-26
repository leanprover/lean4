module
import Init.Data.UInt.BitCounts
import Init.Data.SInt.BitCounts

/-! Kernel, interpreted, and native checks for unsigned and signed word zero counts. -/

private def reference (w n : Nat) : Nat × Nat := Id.run do
  let mut leading := 0
  let mut trailing := 0
  for i in [:w] do
    if leading == i && !n.testBit (w - 1 - i) then leading := leading + 1
    if trailing == i && !n.testBit i then trailing := trailing + 1
  return (leading, trailing)

private def checkUInt8 (n : Nat) : IO Unit := do
  let x := UInt8.ofNat n
  let (leading, trailing) := reference 8 x.toNat
  unless x.clz.toNat == leading && x.ctz.toNat == trailing &&
      x.toInt8.clz == x.clz && x.toInt8.ctz == x.ctz &&
      x.log2.toNat == (if x == 0 then 0 else 8 - (leading + 1)) do
    throw <| IO.userError s!"UInt8: {n}"

private def checkUInt16 (n : Nat) : IO Unit := do
  let x := UInt16.ofNat n
  let (leading, trailing) := reference 16 x.toNat
  unless x.clz.toNat == leading && x.ctz.toNat == trailing &&
      x.toInt16.clz == x.clz && x.toInt16.ctz == x.ctz &&
      x.log2.toNat == (if x == 0 then 0 else 16 - (leading + 1)) do
    throw <| IO.userError s!"UInt16: {n}"

private def checkUInt32 (n : Nat) : IO Unit := do
  let x := UInt32.ofNat n
  let (leading, trailing) := reference 32 x.toNat
  unless x.clz.toNat == leading && x.ctz.toNat == trailing &&
      x.toInt32.clz == x.clz && x.toInt32.ctz == x.ctz &&
      x.log2.toNat == (if x == 0 then 0 else 32 - (leading + 1)) do
    throw <| IO.userError s!"UInt32: {n}"

private def checkUInt64 (n : Nat) : IO Unit := do
  let x := UInt64.ofNat n
  let (leading, trailing) := reference 64 x.toNat
  unless x.clz.toNat == leading && x.ctz.toNat == trailing &&
      x.toInt64.clz == x.clz && x.toInt64.ctz == x.ctz &&
      x.log2.toNat == (if x == 0 then 0 else 64 - (leading + 1)) do
    throw <| IO.userError s!"UInt64: {n}"

private def checkUSize (n : Nat) : IO Unit := do
  let x := USize.ofNat n
  let (leading, trailing) := reference System.Platform.numBits x.toNat
  unless x.clz.toNat == leading && x.ctz.toNat == trailing &&
      x.toISize.clz == x.clz && x.toISize.ctz == x.ctz &&
      x.log2.toNat == (if x == 0 then 0 else System.Platform.numBits - (leading + 1)) do
    throw <| IO.userError s!"USize: {n}"

example : (UInt8.ofNat 0).ctz = 8 := rfl
example : (UInt8.ofNat 0).clz = 8 := rfl
example : (UInt8.ofNat (1 <<< (8 - 1))).ctz = 8 - 1 := rfl
example : (UInt8.ofNat (1 <<< (8 - 1))).clz = 0 := rfl
example : (Int8.ofInt (-1)).clz = 0 := rfl
example : (Int8.ofInt (-1)).ctz = 0 := rfl
example : (UInt8.ofNat 176).ctz = 4 := rfl
example : (UInt8.ofNat 176).clz = 0 := rfl
example : Int8.minValue.ctz = 7 := rfl
example : Int8.minValue.clz = 0 := rfl
example : (Int8.ofInt 48).clz = 2 := rfl
example : (UInt8.ofNat 48).ctz = 4 ∧ (UInt8.ofNat 48).clz = 2 := by decide

example : (UInt16.ofNat 0).ctz = 16 := rfl
example : (UInt16.ofNat 0).clz = 16 := rfl
example : (UInt16.ofNat (1 <<< (16 - 1))).ctz = 16 - 1 := rfl
example : (UInt16.ofNat (1 <<< (16 - 1))).clz = 0 := rfl
example : (Int16.ofInt (-1)).clz = 0 := rfl
example : (Int16.ofInt (-1)).ctz = 0 := rfl
example : (UInt16.ofNat 176).ctz = 4 := rfl
example : (UInt16.ofNat 176).clz = 8 := rfl
example : Int16.minValue.ctz = 15 := rfl
example : Int16.minValue.clz = 0 := rfl
example : (Int16.ofInt 48).clz = 10 := rfl
example : (UInt16.ofNat 48).ctz = 4 ∧ (UInt16.ofNat 48).clz = 10 := by decide

example : (UInt32.ofNat 0).ctz = 32 := rfl
example : (UInt32.ofNat 0).clz = 32 := rfl
example : (UInt32.ofNat (1 <<< (32 - 1))).ctz = 32 - 1 := rfl
example : (UInt32.ofNat (1 <<< (32 - 1))).clz = 0 := rfl
example : (Int32.ofInt (-1)).clz = 0 := rfl
example : (Int32.ofInt (-1)).ctz = 0 := rfl
example : (UInt32.ofNat 176).ctz = 4 := rfl
example : (UInt32.ofNat 176).clz = 24 := rfl
example : Int32.minValue.ctz = 31 := rfl
example : Int32.minValue.clz = 0 := rfl
example : (Int32.ofInt 48).clz = 26 := rfl
example : (UInt32.ofNat 48).ctz = 4 ∧ (UInt32.ofNat 48).clz = 26 := by decide

example : (UInt64.ofNat 0).ctz = 64 := rfl
example : (UInt64.ofNat 0).clz = 64 := rfl
example : (UInt64.ofNat (1 <<< (64 - 1))).ctz = 64 - 1 := rfl
example : (UInt64.ofNat (1 <<< (64 - 1))).clz = 0 := rfl
example : (Int64.ofInt (-1)).clz = 0 := rfl
example : (Int64.ofInt (-1)).ctz = 0 := rfl
example : (UInt64.ofNat 176).ctz = 4 := rfl
example : (UInt64.ofNat 176).clz = 56 := rfl
example : Int64.minValue.ctz = 63 := rfl
example : Int64.minValue.clz = 0 := rfl
example : (Int64.ofInt 48).clz = 58 := rfl
example : (UInt64.ofNat 48).ctz = 4 ∧ (UInt64.ofNat 48).clz = 58 := by decide

public def main : IO Unit := do
  unless (0 : Nat).log2 == 0 && (1 : Nat).log2 == 0 do
    throw <| IO.userError "Nat.log2: zero or one"
  -- Check both possible scalar/bignum boundaries and nearby heap values.
  for k in [30, 31, 32, 62, 63, 64, 65] do
    for (n, expected) in [((1 <<< k) - 1, k - 1), (1 <<< k, k), ((1 <<< k) + 1, k)] do
      unless n.log2 == expected do
        throw <| IO.userError s!"Nat.log2: {n}"
  for n in [:256] do
    checkUInt8 n
    checkUInt16 n
    checkUInt32 n
    checkUInt64 n
    checkUSize n
  for k in [:65] do
    for n in [1 <<< k, (1 <<< k) - 1, (1 <<< k) + 1, 3 <<< k] do
      checkUInt8 n
      checkUInt16 n
      checkUInt32 n
      checkUInt64 n
      checkUSize n
  let mut seed : UInt64 := 0x9e3779b97f4a7c15
  for _ in [:1000] do
    seed := seed * 6364136223846793005 + 1442695040888963407
    checkUInt8 seed.toNat
    checkUInt16 seed.toNat
    checkUInt32 seed.toNat
    checkUInt64 seed.toNat
    checkUSize seed.toNat
