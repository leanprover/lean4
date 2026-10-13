/-!
Tests that `ByteArray.markLinear` and `FloatArray.markLinear` preserve the semantics of the array
they mark and that the marker survives the reallocation that `push` performs when the capacity is
exhausted.
-/

def growBytes (n : Nat) : ByteArray := Id.run do
  let mut bs := (ByteArray.emptyWithCapacity 1).markLinear
  for i in 0...n do
    bs := bs.push i.toUInt8
  return bs

def fillBytes (n : Nat) : ByteArray := Id.run do
  let mut bs := (growBytes n).markLinear
  for i in 0...n do
    bs := bs.set! i (2 * i).toUInt8
  return bs

def growFloats (n : Nat) : FloatArray := Id.run do
  let mut ds := (FloatArray.emptyWithCapacity 1).markLinear
  for i in 0...n do
    ds := ds.push i.toFloat
  return ds

def fillFloats (n : Nat) : FloatArray := Id.run do
  let mut ds := (growFloats n).markLinear
  for i in 0...n do
    ds := ds.set! i (2 * i).toFloat
  return ds

def main : IO Unit := do
  IO.println (growBytes 5).toList
  IO.println (fillBytes 5).toList
  IO.println (growFloats 5)
  IO.println (fillFloats 5)
