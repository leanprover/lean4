module

/-!
Tests for `BitVec.ofNat w k` literals whose width `w` is symbolic. `grind` keeps `BitVec`
literals in the `OfNat.ofNat` form, and terms spelled `k#w` must reach that form whether they
come from the input, from a theorem pattern, or from an instance.
-/

/-
The identity element of `|||` and `^^^` is fixed by the `Std.LawfulIdentity` instances, which
spell it `0#w`. The AC module must internalize it in the `OfNat.ofNat` form (`0`, not `0#w`).
-/

/-- trace: [grind.debug.ac.op] HOr.hOr, comm: true, idempotent: true, neutral?: 0 -/
#guard_msgs in
set_option trace.grind.debug.ac.op true in
example (x y : BitVec w) : x ||| y = y ||| x := by
  grind

/-- trace: [grind.debug.ac.op] HXor.hXor, comm: true, idempotent: false, neutral?: 0 -/
#guard_msgs in
set_option trace.grind.debug.ac.op true in
example (x y : BitVec w) : x ^^^ y = y ^^^ x := by
  grind

set_option backward.grind.normalizer false

-- Patterns are normalized when the attribute is set, so the option must be set first.
attribute [grind =] BitVec.sdiv_zero

example (x : BitVec 32) : x.sdiv 0 = 0 := by
  grind

example (x : BitVec 32) : x.sdiv 0#32 = 0#32 := by
  grind
