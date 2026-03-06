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
import Init.Data.Nat
import Init.Data.List.TakeDrop
import all Init.Data.Repr
import Init.Data.UInt.Lemmas
import Std.Tactic.Do
import Init.Data.String.Lemmas.FindPos
import Init.Data.List.Sublist
import Init.Data.List.Nat.Sublist

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

theorem toNat_digitChar_of_lt_ten {n : Nat} (hn : n < 10) : n.digitChar.toNat = 48 + n :=
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => by simp [digitChar]
  | _ + 10 => by omega

theorem toNat_digitChar_sub_eq_of_lt_ten {n : Nat} (hn : n < 10) : n.digitChar.toNat - 48 = n :=
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => by simp [digitChar]
  | _ + 10 => by omega

theorem toDigits_mul_add {b n k : Nat} (hn : 0 < n) (hb : 1 < b) (hk : k < b) :
    toDigits b (b * n + k) = toDigits b n ++ [digitChar k] := by
  rw [toDigits_of_base_le hb]
  · congr
    · rw [Nat.mul_add_div (by omega), Nat.div_eq_zero_iff.2 (by omega), Nat.add_zero]
    · simpa using Nat.mod_eq_of_lt hk
  · exact Nat.le_trans (Nat.le_mul_of_pos_right _ hn) (Nat.le_add_right ..)

def toDigitsSane (b : Nat) (n : Nat) (hb : 1 < b) : List Nat :=
  if h : n = 0 then
    []
  else
    have : n / b < n := Nat.div_lt_self (by omega) hb
    toDigitsSane b (n / b) hb ++ [n % b]

@[simp]
theorem toDigitsSane_zero {b : Nat} {hb : 1 < b} : toDigitsSane b 0 hb = [] := by
  simp [toDigitsSane]

theorem toDigitsSane_mul_add {b n k : Nat} {hb : 1 < b} (hn : 0 < n) (hk : k < b) :
    toDigitsSane b (b * n + k) hb = toDigitsSane b n hb ++ [k] := by
  rw [toDigitsSane, dif_neg]
  · simp [Nat.mod_eq_of_lt hk]
    rw [Nat.mul_add_div (by omega), Nat.div_eq_zero_iff.2 (Or.inr hk), Nat.add_zero]
  · rw [Nat.add_eq_zero_iff, Nat.mul_eq_zero]
    omega

theorem toDigitsSane_of_lt {b k : Nat} {hb : 1 < b} (hk₀ : k ≠ 0) (hk : k < b) :
    toDigitsSane b k hb = [k] := by
  rw [toDigitsSane, dif_neg hk₀, toDigitsSane, dif_pos (Nat.div_eq_zero_iff.2 (Or.inr hk))]
  simp [Nat.mod_eq_of_lt hk]

def toDigits' (b : Nat) (n : Nat) (hb : 1 < b) : List Char :=
  if n = 0 then
    ['0']
  else
    (toDigitsSane b n hb).map Nat.digitChar

theorem base_induction {P : Nat → Prop} {n : Nat} (b : Nat) (hb : 1 < b) (single : ∀ m, m < b → P m)
    (digit : ∀ m k, k < b → 0 < m → P m → P (b * m + k)) : P n := by
  induction n using Nat.strongRecOn with | ind n ih
  by_cases hn : n < b
  · exact single _ hn
  · have := Nat.div_add_mod n b
    rw [← this]
    apply digit _ _ (Nat.mod_lt _ (by omega)) _ (ih _ _)
    · exact Nat.div_pos (Nat.not_lt.1 hn) (by omega)
    · exact Nat.div_lt_self (by omega) (by omega)

theorem toDigits_eq_toDigits' {n b : Nat} (hb : 1 < b) : toDigits b n = toDigits' b n hb := by
  rw [toDigits']
  split <;> rename_i hn
  · simp_all
  · induction n using base_induction b hb with
    | single n hn' =>
      rw [toDigitsSane, dif_neg hn, toDigitsSane, dif_pos (Nat.div_eq_zero_iff.2 (Or.inr hn'))]
      simp [toDigits_eq_singleton_iff hb, hn', Nat.mod_eq_of_lt hn']
    | digit m k hk hm ih =>
      rw [toDigits_mul_add hm hb hk, ih (Nat.pos_iff_ne_zero.1 hm), toDigitsSane_mul_add hm hk,
        List.map_append, List.map_singleton]

end Nat

namespace Char

@[simp]
theorem val_toNat {c : Char} : c.val.toNat = c.toNat := rfl

theorem val_inj {c d : Char} : c.val = d.val ↔ c = d :=
  Char.ext_iff.symm

theorem toNat_inj {c d : Char} : c.toNat = d.toNat ↔ c = d := by
  simp [← Char.val_toNat, ← Char.val_inj, ← UInt32.toNat_inj]

theorem isDigit_iff_toNat {c : Char} : c.isDigit ↔ '0'.toNat ≤ c.toNat ∧ c.toNat ≤ '9'.toNat := by
  simp [isDigit, UInt32.le_iff_toNat_le]

end Char

namespace List

theorem getLast?_cons_of_ne_nil {x : α} {xs : List α} (h : xs ≠ []) : (x::xs).getLast? = xs.getLast? := by
  cases xs <;> simp_all

theorem mem_of_mem_dropWhile {a : α} {p : α → Bool} {l : List α} (h : a ∈ l.dropWhile p) : a ∈ l := by
  induction l with
  | nil => simp at h
  | cons hd tl ih =>
    by_cases hhd : p hd
    · rw [dropWhile_cons_of_pos hhd] at h
      simp [ih h]
    · rwa [dropWhile_cons_of_neg hhd] at h

theorem infix_append_singleton_iff {a : α} {l m : List α} : l <:+: m ++ [a] ↔ l <:+: m ∨ l <:+ (m ++ [a]) := by
  rw [← List.reverse_infix, List.reverse_append, List.reverse_singleton, List.singleton_append,
    List.infix_cons_iff, ← List.singleton_append]
  rw (occs := [1]) [← List.reverse_singleton]
  rw [← List.reverse_append, List.reverse_prefix, List.reverse_infix, or_comm]

theorem suffix_iff_exists_append {l₁ l₂ : List α} : l₁ <:+ l₂ ↔ ∃ l₃, l₂ = l₃ ++ l₁ := by
  refine ⟨?_, ?_⟩
  · rw [suffix_iff_eq_append]
    intro h
    rw [← h]
    simp
  · rintro ⟨l₃, rfl⟩
    exact suffix_append l₃ l₁

theorem suffix_append_self_iff {l₁ l₂ m : List α} : l₁ ++ m <:+ l₂ ++ m ↔ l₁ <:+ l₂ := by
  simp only [suffix_iff_exists_append]
  refine ⟨?_, ?_⟩
  · rintro ⟨l₃, h⟩
    refine ⟨l₃, by simpa [← List.append_assoc] using h⟩
  · rintro ⟨l₃, rfl⟩
    refine ⟨l₃, by simp⟩

theorem suffix_append_inj_of_length_eq {l₁ l₂ m₁ m₂ : List α} (hm : m₁.length = m₂.length) :
    l₁ ++ m₁ <:+ l₂ ++ m₂ ↔ l₁ <:+ l₂ ∧ m₁ = m₂ := by
  simp only [suffix_iff_exists_append]
  refine ⟨?_, ?_⟩
  · rintro ⟨l₃, h⟩
    rw [← List.append_assoc] at h
    obtain ⟨rfl, rfl⟩ := List.append_inj' h hm.symm
    refine ⟨⟨l₃, by simp⟩, by simp⟩
  · rintro ⟨⟨l₃, rfl⟩, rfl⟩
    refine ⟨l₃, by simp⟩

theorem singleton_suffix_iff_getLast?_eq_some {a : α} {l : List α} : [a] <:+ l ↔ l.getLast? = some a := by
  rw [suffix_iff_exists_append, getLast?_eq_some_iff]

end List

namespace String.Slice

open Std.Do in
set_option mvcgen.warning false in
theorem isNat_iff {s : String.Slice} :
    s.isNat = true ↔
        s.isEmpty = false ∧
        (∀ c ∈ s.copy.toList, c.isDigit ∨ c = '_') ∧
        ¬(['_', '_'] <:+: s.copy.toList) ∧
        s.copy.toList.head? ≠ some '_' ∧
        s.copy.toList.getLast? ≠ some '_' := by
  generalize h : s.isNat = res
  apply Id.of_wp_run_eq h
  mvcgen
  case vc1.inv =>
    exact StringSliceInvariant.withEarlyReturn
      (fun pos lastWasDigit => ⌜∀ t₁ t₂, pos.Splits t₁ t₂ →
          (lastWasDigit = t₁.toList.getLast?.any Char.isDigit ∧ (∀ c ∈ t₁.toList, c.isDigit ∨ c = '_') ∧ ¬(['_', '_'] <:+: t₁.toList)
          ∧ t₁.toList.head?.all (· != '_'))⌝)
      (fun res lastWasDigit => ⌜res = false ∧ ((∃ c ∈ s.copy.toList, c.isDigit = false ∧ c ≠ '_') ∨ s.copy.toList.head? = some '_' ∨ ['_', '_'] <:+: s.copy.toList)⌝)
  next pos _ hp lastWasDigit hget hl ih =>
    subst lastWasDigit
    simp [hp] at ⊢ ih hl
    obtain ⟨t₁, t₂, h⟩ : ∃ t₁ t₂, pos.Splits t₁ t₂ := ⟨_, _, pos.splits⟩
    obtain ⟨t₂, rfl⟩ := h.exists_eq_singleton_append hp
    by_cases hp' : pos = s.startPos
    · subst hp'
      simp at h
      refine Or.inr (Or.inl ?_)
      rw [← h.2]
      simp [hget]
    · obtain ⟨t₁, rfl⟩ := h.exists_eq_append_singleton_of_ne_startPos hp'
      have := ih.2 _ _ h
      simp [hl] at this
      have hx := this.2.1 ((pos.prev hp').get (by simp)) (by simp)
      simp [this.1] at hx
      rw [hx, hget] at h
      refine Or.inr (Or.inr ?_)
      rw [h.eq_append]
      simp only [↓Char.isValue, String.reduceSingleton, toList_append, String.reduceToList,
        List.cons_append, List.nil_append, List.append_assoc]
      apply List.infix_append_of_infix_right
      apply List.IsPrefix.isInfix
      simp
  next pos _ hp lastWasDigit hget hl ih =>
    subst lastWasDigit
    simp [hp] at ⊢ ih hl
    simp [hl] at ih
    intro t₁ t₂ h
    obtain ⟨t₁, rfl⟩ := h.exists_eq_append_singleton hp
    have := ih.2 _ _ h.of_next
    simp [Option.all_eq_true, Option.any_eq_true] at this
    simp [hget]
    refine ⟨?_, ?_⟩
    · rintro c (hc|rfl)
      · exact this.2.1 _ hc
      · simp
    · generalize t₁.toList = l at *
      match l with
      | [] => simp at this
      | x::l =>
        simp at this
        simp [this.2.2]
        rw [← List.cons_append, List.infix_append_singleton_iff, not_or]
        simp [this.2.2.1]
        rw [← List.cons_append, ← List.singleton_append, List.suffix_append_self_iff,
          List.singleton_suffix_iff_getLast?_eq_some]
        obtain ⟨c, hc, hc'⟩ := this.1
        simp [hc]
        rintro rfl
        simp at hc'
  next pos _ hp lastWasDigit hget hget' ih =>
    subst lastWasDigit
    simp [hp] at ⊢ ih
    intro t₁ t₂ h
    obtain ⟨t₁, rfl⟩ := h.exists_eq_append_singleton hp
    have := ih.2 _ _ h.of_next
    simp [hget']
    refine ⟨?_, ?_, ?_⟩
    · rintro c (hc|rfl)
      · exact this.2.1 _ hc
      · simp [hget']
    · rw [List.infix_append_singleton_iff]
      simp [this.2.2.1]
      rw [← List.singleton_append, List.suffix_append_inj_of_length_eq (by simp)]
      simp [Ne.symm hget]
    · match ht : t₁.toList.head? with
      | none => simp [hget]
      | some q => simpa [ht] using this.2.2.2
  next pos _ hp lastWasDigit hget hget' ih =>
    subst lastWasDigit
    simp
    obtain ⟨t₁, t₂, h⟩ : ∃ t₁ t₂, pos.Splits t₁ t₂ := ⟨_, _, pos.splits⟩
    obtain ⟨t₂, rfl⟩ := h.exists_eq_singleton_append hp
    refine Or.inl ?_
    simp [h.eq_append]
    exact ⟨pos.get hp, by simp [hget', hget]⟩
  next => simp
  next r hr ih =>
    rcases r with ⟨r₁, r₂⟩
    simp at hr
    simp [hr] at ⊢ ih
    change r₂ = true ↔
            s.isEmpty = false ∧
              (∀ (c : Char), c ∈ s.copy.toList → c.isDigit = true ∨ c = '_') ∧
                ¬['_', '_'] <:+: s.copy.toList ∧
                  ¬s.copy.toList.head? = some '_' ∧ ¬s.copy.toList.getLast? = some '_'
    simp [ih.1]
    refine ⟨fun h => ?_, ?_⟩
    · simp [Option.any_eq_true] at h
      obtain ⟨c, ⟨hc₁, hc₂⟩⟩ := h
      have := s.copy.toList.getLast?_isSome
      simp [hc₁] at this
      simp [Option.all_eq_true] at ih
      refine ⟨this, ih.2.1, ih.2.2.1, ?_, ?_⟩
      · match hx : s.copy.toList.head? with
        | none => simp
        | some z => simpa using ih.2.2.2 _ hx
      · simp [hc₁]
        rintro rfl
        simp at hc₂
    · rintro ⟨h₁, h₂, h₃, h₄, h₅⟩
      simp [Option.any_eq_true]
      match hy : s.copy.toList.getLast? with
      | none => simp [h₁] at hy
      | some z =>
        simp
        have := ih.2.1 _ (List.mem_of_getLast? hy)
        simp [hy] at h₅
        simpa [h₅] using this
  next _ r hr ih =>
    simp [hr] at ⊢ ih
    simp [ih.1]
    obtain (⟨c, hc₁, hc₂, hc₃⟩|h|h) := ih.2
    · intro hemp hcont
      have := hcont c hc₁
      simp [hc₂, hc₃] at this
    · intro hemp h₁ h₂ h₃
      simp [h] at h₃
    · simp [h]

theorem isDigit_of_isNat {s : String.Slice} (h : s.isNat = true) :
    ∀ c ∈ s.copy.toList.filter (· != '_'), c.isDigit := by
  rw [isNat_iff] at h
  obtain ⟨_, ⟨h', -, -, -⟩⟩ := h
  simpa using fun h hc hc' => by simpa [hc'] using h' h hc

theorem toNat?_eq_some_iff {s : String.Slice} {n : Nat} :
    s.toNat? = some n ↔ s.isNat ∧
      (s.copy.toList.filter (· != '_')).dropWhile (· == '0') = (Nat.toDigitsSane 10 n (by decide)).map Nat.digitChar := by
  rw [toNat?]
  split <;> rename_i h
  · simp [h]
    have : (fun n c => if c = '_' then n else n * 10 + (c.toNat - 48)) =
        fun n c => if (c != '_') = true then n * 10 + (c.toNat - 48) else n := by
      ext n c
      simp
    rw [this, ← List.foldl_filter]
    have h₁ : ∀ c, ((s.copy.toList.filter (· != '_')).dropWhile (· == '0')).head? = some c → c ≠ '0' := by
      intro c hc
      simpa [hc] using List.head?_dropWhile_not (l := s.copy.toList.filter (· != '_')) (p := (· == '0'))
    have h₂ : ∀ c ∈ ((s.copy.toList.filter (· != '_')).dropWhile (· == '0')), c.isDigit := by
      intro c hc
      have := List.mem_of_mem_dropWhile hc
      exact isDigit_of_isNat h _ this
    generalize (s.copy.toList.filter (· != '_')) = l at *
    have hx : l.foldl (init := 0) (fun n c => n * 10 + (c.toNat - 48)) =
        (l.dropWhile (· == '0')).foldl (init := 0) (fun n c => n * 10 + (c.toNat - 48)) := by
      clear h₁ h₂
      induction l with
      | nil => simp
      | cons hd tl ih =>
        by_cases hhd : hd = '0'
        · subst hhd
          rw [List.dropWhile_cons_of_pos (by simp)]
          simp [ih]
        · rw [List.dropWhile_cons_of_neg (by simpa)]
    rw [hx]
    generalize l.dropWhile (· == '0') = l at *
    clear this s h hx
    refine ⟨?_, ?_⟩
    · rintro rfl
      rw [← List.reverse_reverse l] at *
      rw [List.foldl_reverse]
      generalize l.reverse = l at *
      simp only [List.head?_reverse, ↓Char.isValue, ne_eq, List.mem_reverse] at h₁ h₂
      induction l with
      | nil => simp
      | cons hd tl ih =>
        by_cases htl : tl = []
        · simp_all
          simp [Char.isDigit_iff_toNat, ← Char.toNat_inj] at h₁ h₂
          rw [Nat.toDigitsSane_of_lt (by omega) (by omega)]
          simp [← Char.toNat_inj]
          rw [Nat.toNat_digitChar_of_lt_ten (by omega)]
          omega
        · simp [List.getLast?_cons_of_ne_nil htl] at h₁
          simp at h₂
          obtain ⟨h₂, h₂'⟩ := h₂
          simp [Char.isDigit_iff_toNat] at h₂
          simp
          rw [Nat.mul_comm, Nat.toDigitsSane_mul_add _ (by omega), ih h₁ h₂']
          · simp [← Char.toNat_inj]
            rw [Nat.toNat_digitChar_of_lt_ten (by omega)]
            omega
          · clear hd ih h₂
            induction tl with
            | nil => simp at htl
            | cons ht tl ih =>
              by_cases htl' : tl = []
              · simp [htl'] at  ⊢ h₁
                simp [← Char.toNat_inj] at h₁
                simp [Char.isDigit_iff_toNat] at h₂'
                omega
              · rw [List.getLast?_cons_of_ne_nil htl'] at h₁
                simp at h₂'
                have := ih htl' h₁ h₂'.2
                simp
                omega
    · rintro rfl
      clear h₁ h₂
      have : 1 < 10 := by decide
      by_cases hn : n = 0
      · simp_all
      · induction n using Nat.base_induction 10 this with
        | single m hm =>
          simp [Nat.toDigitsSane_of_lt hn hm]
          rw [Nat.toNat_digitChar_sub_eq_of_lt_ten hm]
        | digit m k hk hm ih =>
          rw [Nat.toDigitsSane_mul_add hm hk]
          simp [ih (Nat.pos_iff_ne_zero.1 hm)]
          rw [Nat.toNat_digitChar_sub_eq_of_lt_ten hk, Nat.mul_comm]
  · simp_all

end String.Slice
