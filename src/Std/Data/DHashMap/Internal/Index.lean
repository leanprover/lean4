/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.UInt.Bitwise
import Init.ByCases
import Init.Data.UInt.Lemmas

public section

/-!
This is an internal implementation file of the hash map. Users of the hash map should not rely on
the contents of this file.

File contents: mapping a hash to a hash map bucket
-/

set_option linter.missingDocs true
set_option autoImplicit false

namespace Std.DHashMap.Internal

/-- Scrambles low-range hash codes while folding high-bit entropy into the indexing bits. -/
@[inline]
def scrambleHash (hash : UInt64) : UInt64 :=
  let fold := hash ^^^ (hash >>> 32)
  let folded := fold ^^^ (fold >>> 16)
  -- Low-range hashes commonly come from integer identities; wider hashes usually have entropy.
  if hash >>> 24 == 0 then
    -- Keep small-table indices local, but split the low-range cluster in larger tables.
    if hash >>> 7 == 0 then
      hash ^^^ ((hash &&& 0x40) <<< 1)
    else
      hash * 0x9e3779b97f4a7c15
  else
    folded

-- Note that this indexing scheme always produces a valid index, but it only has a chance of
-- returning every index if sz is a power of two.
/--
`sz` is an explicit parameter because having it inferred from `h` can lead to suboptimal IR,
cf. https://github.com/leanprover/lean4/issues/4157
-/
@[irreducible, inline, expose] def mkIdx (sz : Nat) (h : 0 < sz) (hash : UInt64) :
    { u : USize // u.toNat < sz } :=
  ⟨(scrambleHash hash).toUSize &&& (USize.ofNat sz - 1), by
    -- This proof is a good test for our USize API
    by_cases h' : sz < USize.size
    · rw [USize.toNat_and, USize.toNat_sub_of_le, USize.toNat_ofNat_of_lt' h']
      · exact Nat.lt_of_le_of_lt Nat.and_le_right (Nat.sub_lt h (by simp))
      · simp [USize.le_iff_toNat_le, Nat.mod_eq_of_lt h', Nat.succ_le_of_lt h]
    · exact Nat.lt_of_lt_of_le (USize.toNat_lt_size _) (Nat.le_of_not_lt h')⟩

end Std.DHashMap.Internal
