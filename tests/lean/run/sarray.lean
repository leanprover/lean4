def mkByteArray (n : Nat) : ByteArray := Id.run <| do
  let mut r := {}
  for i in [:n] do
    r := r.push (UInt8.ofNat i)
  return r

def tst1 (n : Nat) (expected : UInt32) : IO Unit := do
  let bs := mkByteArray n
  let sum := bs.foldl (init := 0) fun s b => s + b.toUInt32
  assert! sum == expected
  IO.println sum

#eval tst1 100 4950

def tst2 (n : Nat) (expected : UInt32) : IO Unit := do
  let bs := mkByteArray n
  let mut sum := 0
  for b in bs do
    sum := sum + b.toUInt32
  assert! sum == expected
  IO.println sum

#eval tst2 100 4950

def tst3 (n : Nat) (expected : UInt32) : IO Unit := do
  let bs := mkByteArray n
  let mut sum := 0
  for i in [:bs.size] do
    sum := sum + bs[i]!.toUInt32
  assert! sum == expected
  IO.println sum

#eval tst3 100 4950

set_option trace.compiler.ir.result true in
def computeByteHash (bytes : ByteArray) :=
   bytes.foldl (init := 1723) fun h b => mixHash h (hash b)
