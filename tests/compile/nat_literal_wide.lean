/-! `Nat` literals on both sides of `2^32`, `2^63` and `2^64`, the boundaries where the C emitter
and `ExtractClosed` change how a literal is produced.  Each is added to a run-time value, so the
literals below `2^63` are emitted where they are used; from `2^63` on, `ExtractClosed` hoists them
into closed terms. -/

@[noinline] def lits (i : Nat) : List Nat :=
  [i + 4294967295, i + 4294967296, i + 4294967297,
   i + 9223372036854775807, i + 9223372036854775808,
   i + 18446744073709551615, i + 18446744073709551616]

def main (args : List String) : IO Unit := do
  let i := args.length
  for v in lits i do
    IO.println v
  -- The same values computed at run time, from a base the compiler cannot fold.
  let b := i + 2
  let expected := [b ^ 32 - 1, b ^ 32, b ^ 32 + 1, b ^ 63 - 1, b ^ 63, b ^ 64 - 1, b ^ 64].map (i + ·)
  IO.println (lits i == expected)
