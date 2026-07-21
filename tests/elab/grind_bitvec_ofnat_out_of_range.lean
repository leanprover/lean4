/-!
Tests that `grind` reduces out-of-range `OfNat.ofNat` bitvector literals. The `grind` normal
form for bitvector literals is `OfNat.ofNat` (see #14370). If a literal whose value exceeds
`2^w` (e.g. `(17 : BitVec 4)`) is not reduced modulo `2^w`, then `(17 : BitVec 4)` and `1#4`
are treated as two distinct interpreted values.
-/

/--
This example used to expose the bug: merging the two representations of the same value made
`grind` produce an invalid inconsistency proof rejected by the kernel.
-/
example (x : BitVec 4) (_h1 : x = (17 : BitVec 4)) (_h2 : x = 1#4) : True := by
  grind

example (x : BitVec 4) (h : x = (17 : BitVec 4)) : x = 1#4 := by
  grind

/-- Width-zero edge case: every literal must reduce to `0`. -/
example (x : BitVec 0) (h : x = (1 : BitVec 0)) : x = 0#0 := by
  grind

/-- `grind` must still detect genuine disequalities involving out-of-range literals. -/
example (x : BitVec 4) (h1 : x = (17 : BitVec 4)) (h2 : x = 2#4) : False := by
  grind
