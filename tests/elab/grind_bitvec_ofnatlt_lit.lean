/-!
Tests that `grind` handles `BitVec.ofNatLT` literals correctly. The `grind` normal form for
bitvector literals is `OfNat.ofNat` (see #14370), but `BitVec.ofNatLT` literals are not
normalized to this form. Thus, `BitVec.ofNatLT 1 h : BitVec 4` and `1#4` are treated as two
distinct interpreted values.
-/

/--
This example exposes the bug: merging the two representations of the same value makes `grind`
produce an invalid inconsistency proof rejected by the kernel.
-/
example (x : BitVec 4) (_h1 : x = BitVec.ofNatLT 1 (by decide)) (_h2 : x = 1#4) : True := by
  grind

/--
The following two examples are not unsound, just incomplete: `grind` cannot connect the two
representations. They should pass once `ofNatLT` literals are normalized.
-/

example (x : BitVec 4) (h : x = BitVec.ofNatLT 1 (by decide)) : x = 1#4 := by
  grind

open BitVec in
example (x : BitVec 4) (h : x = 1#'(by decide)) : x = 1#4 := by
  grind

/-- `grind` must still detect genuine disequalities involving `ofNatLT` literals. -/
example (x : BitVec 4) (h1 : x = BitVec.ofNatLT 1 (by decide)) (h2 : x = 2#4) : False := by
  grind
