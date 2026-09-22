/-!
Tests that `grind` normalizes `BitVec.ofNat` literals (e.g. `1#4`) to the same canonical
form used for other evaluated bitvector literals. `grind` normalization uses the config
`bitVecOfNat := false`, so `BitVec.reduceOfNat` must rewrite `1#4` to the `OfNat.ofNat`
form; otherwise `1#4` and the result of reducing `0#2 ++ 1#2` are treated as two distinct
interpreted values, and `grind` produces an invalid inconsistency proof rejected by the
kernel.
-/

example (x : BitVec 4) (_h1 : x = 0#2 ++ 1#2) (_h2 : x = 1#4) : True := by
  grind

example (x : BitVec 4) (h : x = 0#2 ++ 1#2) : x = 1#4 := by
  grind

example (x : BitVec 4) (h1 : x = 0#2 ++ 1#2) (h2 : x = 2#4) : False := by
  grind
