def test (a : Nat) : IO Unit :=
  for b in #[0, 1, 14, 15, 16, 17, 31, 32, 33, 63, 64, 65] do
    IO.println f!"{a >>> b}"

def main : IO Unit := do
  test 0
  test 1
  test 0xff
  test 0x100
  test 0x101
  test 0xffff
  test 0x1000_0
  test 0x1000_1
  test 0xffff_ffff
  test 0x1_0000_0000
  test 0x1_0000_0001
  test 0xffff_ffff_ffff_ffff
  test 0x1_0000_0000_0000_0000
  test 0x1_0000_0000_0000_0001
