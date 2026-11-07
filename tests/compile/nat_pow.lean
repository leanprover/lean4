/-- `a ^ n` by repeated multiplication, as a reference for `Nat.pow`. -/
def powRef (a : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => powRef a n * a

/-- Keeps the compiler from folding the powers below at compile time, so that they reach the
runtime's `lean_nat_pow`. -/
@[noinline] def powRuntime (a n : Nat) : Nat := a ^ n

def bases : List Nat :=
  [0, 1, 2, 3, 7, 10, 255, 256, 0xffff, 0x10000, 3037000499, 3037000500,
   0x7fff_ffff, 0x8000_0000, 0xffff_ffff, 0x1_0000_0000, 0x7fff_ffff_ffff_ffff,
   0x8000_0000_0000_0000, 0xffff_ffff_ffff_ffff, 0x1_0000_0000_0000_0000]

def main : IO Unit := do
  let mut bad := 0
  for a in bases do
    for n in [0:70] do
      if a ^ n != powRef a n then
        IO.println s!"mismatch: {a} ^ {n}"
        bad := bad + 1
  IO.println s!"{bad} mismatches"
  -- Around the largest scalar, `2^63 - 1` on 64-bit platforms.
  IO.println (powRuntime 2 62)
  IO.println (powRuntime 2 63)
  IO.println (powRuntime 2 64)
  IO.println (powRuntime 3 39)
  IO.println (powRuntime 3 40)
  IO.println (powRuntime 3037000499 2)
  IO.println (powRuntime 3037000500 2)
  -- Bases 0 and 1, including exponents too large for any other base.
  IO.println (powRuntime 0 0)
  IO.println (powRuntime 0 5)
  IO.println (powRuntime 1 1000)
  IO.println (powRuntime 0 (2 ^ 40))
  IO.println (powRuntime 1 (2 ^ 40))
