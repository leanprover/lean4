/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.String.Slice
import all Init.Data.String.Slice
import Init.Data.String.Lemmas.Iterate
import Init.Data.Nat.ToString
import Init.ByCases

public section

namespace Nat

theorem toDigits_eq_singleton_iff {b n : Nat} {c : Char} (hb : 1 < b) :
    toDigits b n = [c] ↔ n < b ∧ c = digitChar n := by
  rw [toDigits_eq_if hb]
  split
  · simp_all [eq_comm]
  · simp [*]
    apply ne_of_apply_ne List.length
    have := Nat.length_toDigits_pos (b := b) (n := n / b)
    simp [-List.length_eq_zero_iff]
    omega

theorem toNat_digitChar_of_lt_ten {n : Nat} (hn : n < 10) : n.digitChar.toNat = '0'.toNat + n := sorry

-- theorem

theorem base_induction {P : Nat → Prop} {n : Nat} (b : Nat) (hb : 1 < b) (single : ∀ m, m < b → P m)
    (digit : ∀ m k, k < b → P m → P (b * m + k)) : P n := by
  induction n using Nat.strongRecOn with | ind n ih
  by_cases hn : n < b
  · exact single _ hn
  · have := Nat.div_add_mod n b
    rw [← this]
    apply digit _ _ (Nat.mod_lt _ (by omega)) (ih _ _)
    exact Nat.div_lt_self (by omega) (by omega)

end Nat

namespace Char

#check Char.isDigit

theorem isDigit_iff_toNat {c : Char} : c.isDigit ↔ '0'.toNat ≤ c.toNat ∧ c.toNat ≤ '9'.toNat := sorry

theorem toNat_inj {c d : Char} : c.toNat = d.toNat ↔ c = d := sorry

end Char

namespace String.Slice

theorem isEmpty_filter_ne_nil_of_isNat {s : String.Slice} (h : s.isNat = true) :
    s.copy.toList.filter (· != '_') ≠ [] := by
  sorry

theorem isDigit_of_isNat {s : String.Slice} (h : s.isNat = true) :
    ∀ c ∈ s.copy.toList.filter (· != '_'), c.isDigit := sorry

theorem Char.ne_underscore_of_isDigit {c : Char} (h : c.isDigit) : c ≠ '_' := sorry

theorem toNat?_eq_some_iff {s : String.Slice} {n : Nat} :
    s.toNat? = some n ↔ s.isNat ∧ s.copy.toList.filter (· != '_') = Nat.toDigits 10 n := by
  rw [toNat?]
  split <;> rename_i h
  · simp [h]
    have : (fun n c => if c = '_' then n else n * 10 + (c.toNat - 48)) =
        fun n c => if (c != '_') = true then n * 10 + (c.toNat - 48) else n := by
      ext n c
      simp
    rw [this, ← List.foldl_filter]
    have h₁ := isEmpty_filter_ne_nil_of_isNat h
    have h₂ := isDigit_of_isNat h
    generalize s.copy.toList.filter (· != '_') = l at *
    refine ⟨?_, ?_⟩
    · rintro rfl
      sorry

    · rintro rfl
      induction n using Nat.base_induction 10 (by decide) with
      | single m hm =>
        simp [Nat.toDigits_of_lt_base hm]

      | digit => sorry
  · simp_all

end String.Slice
