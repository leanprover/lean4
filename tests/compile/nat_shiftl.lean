/-!
Tests the runtime implementation of `Nat.shiftLeft`, in particular the scalar fast path and its
overflow check around the boundary between small (scalar) and big (GMP) `Nat`s.
-/

def test (a : Nat) : IO Unit :=
  for b in #[0, 1, 14, 15, 16, 17, 29, 30, 31, 32, 33, 61, 62, 63, 64, 65] do
    IO.println f!"{a <<< b}"

def testBig (a b : Nat) : IO Unit :=
  IO.println f!"{a <<< b}"

def main : IO Unit := do
  test 0
  test 1
  test 3
  test 0xff
  test 0x100
  test 0x101
  test 0xffff
  test 0x1000_0
  test 0x1000_1
  test 0x3fff_ffff
  test 0x4000_0000
  test 0xffff_ffff
  test 0x1_0000_0000
  test 0x1_0000_0001
  test 0x3fff_ffff_ffff_ffff
  test 0x4000_0000_0000_0000
  test 0x7fff_ffff_ffff_ffff
  test 0x8000_0000_0000_0000
  test 0xffff_ffff_ffff_ffff
  test 0x1_0000_0000_0000_0000
  test 0x1_0000_0000_0000_0001
  -- shift amounts that exceed a machine word are only supported for `0`
  testBig 0 0x1_0000_0000_0000_0000
