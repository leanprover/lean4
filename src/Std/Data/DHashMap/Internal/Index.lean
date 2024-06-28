/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Std.Init.All

namespace Std.DHashMap.Internal

/--
Scramble the hash code in order to protect against bad hash functions.

Example: if `Hashable Float` was implemented using the "identity" reinterpreting the bit pattern as a `UInt64`,
then the hash codes of all small positive or negative integers would end in around 50 zeroes, meaning that they
all land in bucket 0 in reasonably-sized hash maps.

To counteract this, we xor the hash code with some shifted-down versions of itself, to make sure that all of
the entropy of the hash code appears in the lower 16 bits at least.

The scrambling operation is very fast. It does not have a measurable impact on performance in the insert benchmark.
-/
@[inline]
def scrambleHash (hash : UInt64) : UInt64 :=
  let fold := hash ^^^ (hash >>> 32)
  fold ^^^ (fold >>> 16)

-- Note that this indexing scheme always produces a valid index, but it only has a chance of returning every index if sz is a power of two.
/--
`sz` is an explicit parameter because having it inferred from `h` can lead to suboptimal IR, cf. https://github.com/leanprover/lean4/issues/4157
-/
@[irreducible] def mkIdx (sz : Nat) (h : 0 < sz) (hash : UInt64) : { u : USize // u.toNat < sz } :=
  ⟨(scrambleHash hash).toUSize &&& (sz.toUSize - 1), by
    -- Making this proof significantly less painful will be a good test for our USize API
    by_cases h' : sz < USize.size
    · rw [USize.toNat_and, ← Nat.toUSize_one, USize.toNat_sub_le, Nat.toNat_toUSize]
      · refine Nat.lt_of_le_of_lt Nat.and_le_right (Nat.sub_lt h ?_)
        rw [Nat.toNat_toUSize]
        · exact Nat.one_pos
        · exact Nat.lt_of_le_of_lt h h'
      · exact h'
      · rw [USize.le_def, Fin.le_def]
        change _ ≤ (_ % _)
        rw [Nat.mod_eq_of_lt h', Nat.toUSize, USize.ofNat, Fin.val_ofNat', Nat.mod_eq_of_lt]
        · exact h
        · exact Nat.lt_of_le_of_lt h h'
    · exact Nat.lt_of_lt_of_le USize.toNat_lt' (Nat.le_of_not_lt h')⟩

end Std.DHashMap.Internal
