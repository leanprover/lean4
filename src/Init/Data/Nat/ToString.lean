/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rossel, Paul Reichert
-/
module

prelude
public import Init.Data.Repr
public import Init.Data.Char.Basic
public import Init.Data.ToString.Basic
public import Init.Data.String.Basic
import Init.NotationExtra
import all Init.Data.Repr
import Init.Omega
import Init.RCases
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Bitwise
import Init.Data.Nat.Simproc
import Init.WFTactics
import Init.Data.Char.Lemmas

public section

-- todo: lemmas about `ToString Nat` and `ToString Int`

namespace Nat

variable {b : Nat}


@[simp]
theorem isDigit_digitChar : n.digitChar.isDigit = decide (n < 10) :=
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => by simp [digitChar]
  | _ + 10 => by
    simp only [digitChar, ↓reduceIte, Nat.reduceEqDiff]
    (repeat' split) <;> simp

private theorem isDigit_of_mem_toDigitsCore
    (hc : c ∈ cs → c.isDigit) (hb₁ : 0 < b) (hb₂ : b ≤ 10) (h : c ∈ toDigitsCore b fuel n cs) :
    c.isDigit := by
  induction fuel generalizing n cs with rw [toDigitsCore] at h
  | zero => exact hc h
  | succ _ ih =>
    split at h
    case' isFalse => apply ih (fun h => ?_) h
    all_goals
      cases h with
      | head      => simp [Nat.lt_of_lt_of_le (mod_lt _ hb₁) hb₂]
      | tail _ hm => exact hc hm

theorem isDigit_of_mem_toDigits (hb₁ : 0 < b) (hb₂ : b ≤ 10) (hc : c ∈ toDigits b n) : c.isDigit :=
  isDigit_of_mem_toDigitsCore (fun _ => by contradiction) hb₁ hb₂ hc

private theorem toDigitsCore_of_lt_base (hb : n < b) (hf : n < fuel) :
    toDigitsCore b fuel n cs = n.digitChar :: cs := by
  unfold toDigitsCore
  split <;> simp_all [mod_eq_of_lt]

theorem toDigits_of_lt_base (h : n < b) : toDigits b n = [n.digitChar] :=
  toDigitsCore_of_lt_base h (lt_succ_self _)

@[simp, grind =]
theorem toDigits_zero : (b : Nat) → toDigits b 0 = ['0']
  | 0     => rfl
  | _ + 1 => toDigits_of_lt_base (zero_lt_succ _)

private theorem toDigitsCore_append :
    toDigitsCore b fuel n cs₁ ++ cs₂ = toDigitsCore b fuel n (cs₁ ++ cs₂) := by
  induction fuel generalizing n cs₁ with simp only [toDigitsCore]
  | succ => split <;> simp_all

private theorem toDigitsCore_eq_toDigitsCore_nil_append :
    toDigitsCore b fuel n cs₁ = toDigitsCore b fuel n [] ++ cs₁ := by
  simp [toDigitsCore_append]

private theorem toDigitsCore_eq_of_lt_fuel (hb : 1 < b) (h₁ : n < fuel₁) (h₂ : n < fuel₂) :
    toDigitsCore b fuel₁ n cs = toDigitsCore b fuel₂ n cs := by
  cases fuel₁ <;> cases fuel₂ <;> try contradiction
  simp only [toDigitsCore, Nat.div_eq_zero_iff]
  split
  · simp
  · have := Nat.div_lt_self (by omega : 0 < n) hb
    exact toDigitsCore_eq_of_lt_fuel hb (by omega) (by omega)

private theorem toDigitsCore_toDigitsCore
    (hb : 1 < b) (hn : 0 < n) (hd : d < b) (hf : b * n + d < fuel) (hnf : n < nf) (hdf : d < df) :
    toDigitsCore b nf n (toDigitsCore b df d cs) = toDigitsCore b fuel (b * n + d) cs := by
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    rw [toDigitsCore]
    split
    case isTrue h =>
      have : b ≤ b * n + d := Nat.le_trans (Nat.le_mul_of_pos_right _ hn) (le_add_right _ _)
      cases Nat.div_eq_zero_iff.mp h <;> omega
    case isFalse =>
      have h : (b * n + d) / b = n := by
        rw [mul_add_div (by omega), Nat.div_eq_zero_iff.mpr (.inr hd), Nat.add_zero]
      have := (Nat.lt_mul_iff_one_lt_left hn).mpr hb
      simp only [toDigitsCore_of_lt_base hd hdf, mul_add_mod_self_left, mod_eq_of_lt hd, h]
      apply toDigitsCore_eq_of_lt_fuel hb hnf (by omega)

theorem toDigits_append_toDigits (hb : 1 < b) (hn : 0 < n) (hd : d < b) :
    (toDigits b n) ++ (toDigits b d) = toDigits b (b * n + d) := by
  rw [toDigits, toDigitsCore_append]
  exact toDigitsCore_toDigitsCore hb hn hd (lt_succ_self _) (lt_succ_self _) (lt_succ_self _)

theorem toDigits_of_base_le (hb : 1 < b) (h : b ≤ n) :
    toDigits b n = toDigits b (n / b) ++ [digitChar (n % b)] := by
  have := Nat.div_add_mod n b
  rw (occs := [1]) [← Nat.div_add_mod n b,
    ← toDigits_append_toDigits (by omega) (Nat.div_pos_iff.mpr (by omega)) (Nat.mod_lt n (by omega))]
  rw [toDigits_of_lt_base (n := n % b) (Nat.mod_lt n (by omega))]

theorem toDigits_eq_if (hb : 1 < b) :
    toDigits b n = if n < b then [digitChar n] else toDigits b (n / b) ++ [digitChar (n % b)] := by
  split
  · rw [toDigits_of_lt_base ‹_›]
  · rw [toDigits_of_base_le hb (by omega)]

theorem length_toDigits_pos {b n : Nat} :
    0 < (Nat.toDigits b n).length := by
  simp [toDigits]
  rw [toDigitsCore]
  split
  · simp
  · rw [toDigitsCore_eq_toDigitsCore_nil_append]
    simp

theorem length_toDigits_le_iff {n k : Nat} (hb : 1 < b) (h : 0 < k) :
    (Nat.toDigits b n).length ≤ k ↔ n < b ^ k := by
  match k with
  | 0 => contradiction
  | k + 1 =>
    induction k generalizing n
    · rw [toDigits_eq_if hb]
      split <;> simp [*, length_toDigits_pos, ← Nat.pos_iff_ne_zero, - List.length_eq_zero_iff]
    · rename_i ih
      rw [toDigits_eq_if hb]
      split
      · rename_i hlt
        simp [Nat.pow_add]
        refine Nat.lt_of_lt_of_le hlt ?_
        apply Nat.le_mul_of_pos_left
        apply Nat.mul_pos
        · apply Nat.pow_pos
          omega
        · omega
      · simp [ih (n := n / b) (by omega), Nat.div_lt_iff_lt_mul (k := b) (by omega), Nat.pow_add]

theorem repr_eq_ofList_toDigits {n : Nat} :
    n.repr = .ofList (toDigits 10 n) :=
  (rfl)

theorem toString_eq_ofList_toDigits {n : Nat} :
    toString n = .ofList (toDigits 10 n) :=
  (rfl)

@[simp, grind norm]
theorem toString_eq_repr {n : Nat} :
    toString n = n.repr :=
  (rfl)

@[simp, grind norm]
theorem reprPrec_eq_repr {n i : Nat} :
    reprPrec n i = n.repr :=
  (rfl)

@[simp, grind norm]
theorem repr_eq_repr {n : Nat} :
    repr n = n.repr :=
  (rfl)

theorem repr_of_lt {n : Nat} (h : n < 10) :
    n.repr = .singleton (digitChar n) := by
  rw [repr_eq_ofList_toDigits, toDigits_of_lt_base h, String.singleton_eq_ofList]

theorem repr_of_ge {n : Nat} (h : 10 ≤ n) :
    n.repr = (n / 10).repr ++ .singleton (digitChar (n % 10)) := by
  simp [repr_eq_ofList_toDigits, toDigits_of_base_le (by omega) h, String.singleton_eq_ofList,
    String.ofList_append]

theorem repr_eq_repr_append_repr {n : Nat} (h : 10 ≤ n) :
    n.repr = (n / 10).repr ++ (n % 10).repr := by
  rw [repr_of_ge h, repr_of_lt (n := n % 10) (by omega)]

theorem length_repr_pos {n : Nat} :
    0 < n.repr.length := by
  simpa [repr_eq_ofList_toDigits] using length_toDigits_pos

theorem length_repr_le_iff {n k : Nat} (h : 0 < k) :
    n.repr.length ≤ k ↔ n < 10 ^ k := by
  simpa [repr_eq_ofList_toDigits] using length_toDigits_le_iff (by omega) h

end Nat
