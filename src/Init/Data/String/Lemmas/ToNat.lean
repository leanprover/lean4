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

theorem toNat_digitChar_of_lt_ten {n : Nat} (hn : n < 10) : n.digitChar.toNat = 48 + n :=
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => by simp [digitChar]
  | _ + 10 => by omega

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

end Nat

end -- public section

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

theorem prefix_iff_exists_append {l₁ l₂ : List α} : l₁ <+: l₂ ↔ ∃ l₃, l₂ = l₁ ++ l₃ := by
  refine ⟨?_, ?_⟩
  · rw [prefix_iff_eq_append]
    intro h
    rw [← h]
    simp
  · rintro ⟨l₃, rfl⟩
    exact prefix_append l₁ l₃

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

theorem singleton_prefix_iff_head?_eq_some {a : α} {l : List α} : [a] <+: l ↔ l.head? = some a := by
  simp [prefix_iff_exists_append, head?_eq_some_iff]

theorem filter_bne_eq_self_of_not_mem [BEq α] [LawfulBEq α] {a : α} {l : List α} (h : a ∉ l) :
    l.filter (· != a) = l := by
  rw [List.filter_eq_self]
  intro c hc
  simp only [bne_iff_ne, ne_eq]
  exact fun heq => absurd (heq ▸ hc) h

theorem dropWhile_beq_eq_self_of_head?_ne [BEq α] [LawfulBEq α] {a : α} {l : List α}
    (h : l.head? ≠ some a) : l.dropWhile (· == a) = l := by
  cases l with
  | nil => simp
  | cons hd tl =>
    rw [List.dropWhile_cons_of_neg]
    simpa [beq_iff_eq] using h

end List

public section

namespace String.Slice

structure NoRepetition {α : Type u} (a : α) (l : List α) : Prop where
  not_isInfix : ¬ [a, a] <:+: l

theorem noRepetition_iff {α : Type u} {a : α} {l : List α} : NoRepetition a l ↔ ¬ [a, a] <:+: l :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

theorem NoRepetition.right_of_append {α : Type u} {a : α} {l m : List α} :
    NoRepetition a (l ++ m) → NoRepetition a m := by
  simpa [noRepetition_iff] using mt List.infix_append_of_infix_right

theorem NoRepetition.left_of_append {α : Type u} {a : α} {l m : List α} :
    NoRepetition a (l ++ m) → NoRepetition a l := by
  simpa [noRepetition_iff] using mt List.infix_append_of_infix_left

theorem not_noRepetition_append_of_right {α : Type u} {a : α} {l m : List α} :
    ¬ NoRepetition a m → ¬ NoRepetition a (l ++ m) :=
  mt NoRepetition.right_of_append

theorem not_noRepetition_append_of_left {α : Type u} {a : α} {l m : List α} :
    ¬ NoRepetition a l → ¬ NoRepetition a (l ++ m) :=
  mt NoRepetition.left_of_append

theorem not_noRepetition_append_singleton_of_suffix {α : Type u} {a : α} {l : List α}
    (h : [a] <:+ l) : ¬ NoRepetition a (l ++ [a]) := by
  simpa [noRepetition_iff] using (List.suffix_append_self_iff.2 h).isInfix

theorem NoRepetition.not_isSuffix_of_append_singleton {α : Type u} {a : α} {l : List α} :
    NoRepetition a (l ++ [a]) → ¬ [a] <:+ l := by
  simpa using mt not_noRepetition_append_singleton_of_suffix

theorem NoRepetition.append_singleton_of_not_suffix {α : Type u} {a : α} {l : List α}
    (h : NoRepetition a l) (h' : ¬ [a] <:+ l) : NoRepetition a (l ++ [a]) := by
  simp only [noRepetition_iff, List.infix_append_singleton_iff, not_or] at ⊢ h
  exact ⟨h, by rwa [← List.singleton_append, List.suffix_append_self_iff]⟩

theorem NoRepetition.append_singleton_of_ne {α : Type u} {a b : α} {l : List α}
    (h : NoRepetition a l) (h' : a ≠ b) : NoRepetition a (l ++ [b]) := by
  simp [noRepetition_iff, List.infix_append_singleton_iff] at ⊢ h
  refine ⟨h, ?_⟩
  rw [← List.singleton_append, List.suffix_append_inj_of_length_eq (by simp)]
  simp [h']

@[simp]
theorem noRepetition_singleton {α : Type u} {a b : α} : NoRepetition a [b] := by
  simpa [noRepetition_iff] using fun h => by simpa using h.length_le

theorem noRepetition_cons_append_append_iff {α : Type u} {a : α} {l : List α} :
    NoRepetition a (a :: (l ++ [a])) ↔
      l ≠ [] ∧ ¬ [a, a] <:+: l ∧ l.head? ≠ some a ∧ l.getLast? ≠ some a := by
  simp only [noRepetition_iff, List.infix_cons_iff, List.cons_prefix_cons, true_and,
    List.infix_append_singleton_iff, not_or, ne_eq, ← List.singleton_prefix_iff_head?_eq_some,
    ← List.singleton_suffix_iff_getLast?_eq_some]
  conv => enter [1, 2, 2]; rw [← List.singleton_append, List.suffix_append_self_iff]
  refine ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨?_, h₂, ?_, h₃⟩, fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨?_, h₂, h₄⟩⟩
  · rintro rfl
    simp_all
  · exact fun h => h₁ (List.prefix_append_of_prefix h)
  · cases l <;> simp_all

@[simp]
theorem List.suffix_cons_append {a : α} {l m : List α} : m <:+ a :: (l ++ m) := by
  rw [← List.cons_append]
  exact List.suffix_append (a :: l) m

@[simp]
theorem List.singleton_suffix_append_singleton_iff {a b : α} {l : List α} :
    [a] <:+ l ++ [b] ↔ a = b := by
  refine ⟨fun h => Eq.symm ?_, by rintro rfl; simp⟩
  simpa [List.suffix_iff_exists_append] using h

@[simp]
theorem List.singleton_suffix_cons_append_singleton_iff {a b c : α} {l : List α} :
    [a] <:+ b :: (l ++ [c]) ↔ a = c := by
  rw [← List.cons_append]
  exact singleton_suffix_append_singleton_iff

@[simp]
theorem imp_or_left_iff_true {P Q : Prop} : (P → P ∨ Q) ↔ True := by
  simpa using Or.inl

@[simp]
theorem imp_or_right_iff_true {P Q : Prop} : (Q → P ∨ Q) ↔ True := by
  simpa using Or.inr

@[simp]
theorem forall_or_imp_or_self_right_right {P Q R : α → Prop} :
    (∀ a, P a ∨ Q a → R a ∨ Q a) ↔ (∀ a, P a → R a ∨ Q a) := by
  simp only [or_imp, imp_or_right_iff_true, and_true]

@[simp]
theorem forall_or_imp_or_self_right_left {P Q R : α → Prop} :
    (∀ a, P a ∨ Q a → Q a ∨ R a) ↔ (∀ a, P a → Q a ∨ R a) := by
  simp only [or_imp, imp_or_left_iff_true, and_true]

@[simp]
theorem forall_or_imp_or_self_left_right {P Q R : α → Prop} :
    (∀ a, Q a ∨ P a → R a ∨ Q a) ↔ (∀ a, P a → R a ∨ Q a) := by
  simp only [or_imp, imp_or_right_iff_true, true_and]

@[simp]
theorem forall_or_imp_or_self_left_left {P Q R : α → Prop} :
    (∀ a, Q a ∨ P a → Q a ∨ R a) ↔ (∀ a, P a → Q a ∨ R a) := by
  simp only [or_imp, imp_or_left_iff_true, true_and]

@[simp] theorem forall_eq_or_imp' {P Q : α → Prop} {a' : α} :
    (∀ (a : α), a' = a ∨ Q a → P a) ↔ P a' ∧ ∀ (a : α), Q a → P a := by
  simp only [or_imp, forall_and, forall_eq']

@[simp] theorem forall_or_eq_imp {P Q : α → Prop} :
    (∀ a, Q a ∨ a = a' → P a) ↔ (∀ a, Q a → P a) ∧ P a' := by
  simp only [or_imp, forall_and, forall_eq]

@[simp] theorem forall_or_eq_imp' {P Q : α → Prop} :
    (∀ a, Q a ∨ a' = a → P a) ↔ (∀ a, Q a → P a) ∧ P a' := by
  simp only [or_imp, forall_and, forall_eq']

open Std.Do in
set_option mvcgen.warning false in
theorem isNat_iff' {s : String.Slice} :
    s.isNat = true ↔
        s.copy.toList ≠ [] ∧
        (∀ c ∈ s.copy.toList, c.isDigit ∨ c = '_') ∧
        NoRepetition '_' ('_' :: s.copy.toList ++ ['_']) := by
  generalize h : s.isNat = res
  apply Id.of_wp_run_eq h
  simp only [↓Char.isValue, Bool.not_eq_eq_eq_not, Bool.not_true, forIn_eq_forIn_toList, ne_eq,
    WP.bind, SPred.entails_nil, SPred.down_pure, forall_const]
  mvcgen invariants
  | inv1 => Invariant.withEarlyReturnNewDo
      (fun cursor lastWasDigit => ⌜lastWasDigit = ¬ (['_'] <:+ ('_' :: cursor.prefix)) ∧
        (∀ c ∈ cursor.prefix, c.isDigit ∨ c = '_') ∧ NoRepetition '_' ('_' :: cursor.prefix)⌝)
      (fun res lastWasDigit => ⌜res = false ∧
        ((∃ c ∈ s.copy.toList, c.isDigit = false ∧ c ≠ '_') ∨ ¬ NoRepetition '_' ('_' :: s.copy.toList))⌝)
  next pref c suff h b hc h₁ h₂ =>
    subst hc
    simp only [h₁, ↓Char.isValue, eq_iff_iff, false_iff, Decidable.not_not,
      reduceCtorEq, h, List.mem_append, List.mem_cons, ne_eq, false_and, and_false, exists_const,
      or_false, Option.some.injEq, Bool.false_eq, true_and, and_self_left, exists_eq_left,
      false_or] at ⊢ h₂
    rw [List.append_cons, ← List.cons_append, ← List.cons_append]
    exact Or.inr (not_noRepetition_append_of_left (not_noRepetition_append_singleton_of_suffix h₂.2.1))
  next pref c suff h b hc h₁ h₂ =>
    subst hc
    simp only [h₁, ↓Char.isValue, eq_iff_iff, true_iff, reduceCtorEq, h, List.mem_append,
      List.mem_cons, ne_eq, false_and, and_false, exists_const, or_false, Bool.false_eq_true,
      List.suffix_cons_append, not_true_eq_false, List.not_mem_nil,
      forall_or_imp_or_self_right_right, true_and] at ⊢ h₂
    refine ⟨h₂.2.2.1, ?_⟩
    rw [← List.cons_append]
    exact NoRepetition.append_singleton_of_not_suffix h₂.2.2.2 h₂.2.1
  next pref c suff h b hc hc' h₁ =>
    simp only [↓Char.isValue, eq_iff_iff, reduceCtorEq, h, List.mem_append, List.mem_cons, ne_eq,
      false_and, and_false, exists_const, or_false, List.singleton_suffix_cons_append_singleton_iff,
      Ne.symm hc, not_false_eq_true, List.not_mem_nil, forall_or_eq_imp, hc', true_or, and_true,
      true_and] at ⊢ h₁
    refine ⟨h₁.2.2.1, ?_⟩
    rw [← List.cons_append]
    exact NoRepetition.append_singleton_of_ne h₁.2.2.2 (Ne.symm hc)
  next pref c suff h b hc hc' h₁ => simpa [h] using Or.inl ⟨c, by simp_all⟩
  next => simp
  next r b h₁ h₂ =>
    simp only [h₁, reduceCtorEq, ↓Char.isValue, eq_iff_iff, false_and, Option.some.injEq, ne_eq,
      true_and, exists_eq_left', false_or] at h₂
    simp only [h₂.1, Bool.false_eq_true, toList_eq_nil_iff, copy_eq_empty_iff, Bool.not_eq_true,
      ↓Char.isValue, List.cons_append, false_iff, not_and]
    intro hx hy
    obtain (⟨c, hc₁, hc₂, hc₃⟩|hn) := h₂.2
    · have := hy c
      simp_all
    · rw [← List.cons_append]
      exact not_noRepetition_append_of_left hn
  next r h₁ h₂ =>
    generalize s.copy.toList = l at *
    simp only [h₁, ↓Char.isValue, eq_iff_iff, true_and, reduceCtorEq, ne_eq, false_and,
      exists_const, or_false, List.cons_append] at ⊢ h₂
    rw [h₂.1]
    refine ⟨fun h => ⟨?_, h₂.2.1, ?_⟩, fun ⟨h₁, _, h₂⟩ => ?_⟩
    · rintro rfl
      simp at h
    · rw [← List.cons_append]
      apply NoRepetition.append_singleton_of_not_suffix h₂.2.2 h
    · rw [← List.cons_append] at h₂
      exact h₂.not_isSuffix_of_append_singleton

theorem isNat_iff {s : String.Slice} :
    s.isNat = true ↔
      s.isEmpty = false ∧
      (∀ c ∈ s.copy.toList, c.isDigit ∨ c = '_') ∧
      ¬ ['_', '_'] <:+: s.copy.toList ∧
      s.copy.toList.head? ≠ some '_' ∧
      s.copy.toList.getLast? ≠ some '_' := by
  simp +contextual [isNat_iff', noRepetition_cons_append_append_iff]

theorem isNat_of_isDigit {s : String.Slice} (hne : s.isEmpty = false)
    (hdigit : ∀ c ∈ s.copy.toList, c.isDigit) : s.isNat = true := by
  rw [isNat_iff]
  refine ⟨hne, fun c hc => Or.inl (hdigit c hc), fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := hdigit _ (by simpa using h.subset)
    simp at this
  · have := hdigit _ (s.copy.toList.mem_of_head? h)
    simp at this
  · have := hdigit _ (s.copy.toList.mem_of_getLast? h)
    simp at this

private theorem isDigit_of_isNat {s : String.Slice} (h : s.isNat = true) :
    ∀ c ∈ s.copy.toList.filter (· != '_'), c.isDigit := by
  rw [isNat_iff] at h
  obtain ⟨_, ⟨h', -, -, -⟩⟩ := h
  simpa using fun h hc hc' => by simpa [hc'] using h' h hc

private theorem foldl_dropWhile_zero (l : List Char) :
    l.foldl (init := 0) (fun n c => n * 10 + (c.toNat - 48)) =
    (l.dropWhile (· == '0')).foldl (init := 0) (fun n c => n * 10 + (c.toNat - 48)) := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    by_cases hhd : hd = '0'
    · subst hhd
      rw [List.dropWhile_cons_of_pos (by simp)]
      simp [ih]
    · rw [List.dropWhile_cons_of_neg (by simpa)]

private theorem foldr_base_10_pos {l : List Nat}
    (hne : l ≠ []) (hlast : ∀ d, l.getLast? = some d → d ≠ 0) :
    0 < l.foldr (fun d n => n * 10 + d) 0 := by
  induction l with
  | nil => simp at hne
  | cons hd tl ih =>
    by_cases htl : tl = []
    · simp [htl] at hlast ⊢; omega
    · rw [List.getLast?_cons_of_ne_nil htl] at hlast
      have := ih htl hlast; simp; omega

private theorem eq_toDigitsSane_of_foldl_nat {l : List Nat}
    (hhead : ∀ d, l.head? = some d → d ≠ 0)
    (hdigit : ∀ d ∈ l, d < 10) :
    l.foldl (init := 0) (fun n d => n * 10 + d) = n → l = Nat.toDigitsSane 10 n (by decide) := by
  rintro rfl
  rw [← List.reverse_reverse l] at *
  generalize l.reverse = l at *
  simp only [List.foldl_reverse, List.head?_reverse, List.mem_reverse] at hhead hdigit ⊢
  induction l with
  | nil => simp
  | cons hd tl ih =>
    by_cases htl : tl = []
    · simp_all [Nat.toDigitsSane_of_lt]
    · simp only [List.getLast?_cons_of_ne_nil htl, ne_eq, List.mem_cons,
        forall_eq_or_imp] at hhead hdigit
      obtain ⟨hhd, htl_digit⟩ := hdigit
      simp [Nat.mul_comm, Nat.toDigitsSane_mul_add (foldr_base_10_pos htl hhead) (by omega),
        ih hhead htl_digit]

private theorem digitChar_toNat_sub_48 {c : Char} (h : c.isDigit) :
    Nat.digitChar (c.toNat - 48) = c := by
  simp only [Char.isDigit_iff_toNat, ↓Char.isValue, Char.reduceToNat, ← Char.toNat_inj] at ⊢ h
  rw [Nat.toNat_digitChar_of_lt_ten (by omega)]
  omega

@[simp]
private theorem digitChar_comp_toNat_sub_48 :
    Nat.digitChar ∘ (fun (c : { c : Char // c.isDigit = true }) => c.val.toNat - 48) = Subtype.val := by
  ext1 c
  rcases c with ⟨c, hc⟩
  simp [digitChar_toNat_sub_48 hc]

private theorem eq_map_digitChar_map_toNat_sub_48 {l : List Char} (hdigit : ∀ c ∈ l, c.isDigit) :
    l = (l.map (fun c => c.toNat - 48)).map Nat.digitChar := by
  conv => rhs; rw [← List.unattach_attachWith (H := hdigit)]
  simp only [List.map_unattach, wfParam, List.map_map, digitChar_comp_toNat_sub_48]
  simp

private theorem eq_toDigitsSane_map_of_foldl {l : List Char} {n : Nat}
    (hhead : ∀ c, l.head? = some c → c ≠ '0')
    (hdigit : ∀ c ∈ l, c.isDigit)
    (hfoldl : l.foldl (init := 0) (fun n c => n * 10 + (c.toNat - 48)) = n) :
    l = (Nat.toDigitsSane 10 n (by decide)).map Nat.digitChar := by
  rw [eq_map_digitChar_map_toNat_sub_48 hdigit]
  simp [← Char.toNat_inj, Char.isDigit_iff_toNat] at hhead hdigit
  have lt_ten : ∀ d ∈ l.map (fun c => c.toNat - 48), d < 10 := by
    simpa using fun c hc => by have := hdigit c hc; omega
  have hhead' : ∀ d, (l.map (fun c => c.toNat - 48)).head? = some d → d ≠ 0 := by
    simpa using fun c hc => by have := hdigit c (List.mem_of_head? hc); have := hhead c hc; omega
  rw [eq_toDigitsSane_of_foldl_nat hhead' lt_ten (by simpa [List.foldl_map])]

private theorem foldl_of_eq_toDigitsSane_map {l : List Char} {n : Nat}
    (h : l = (Nat.toDigitsSane 10 n (by decide)).map Nat.digitChar) :
    l.foldl (init := 0) (fun n c => n * 10 + (c.toNat - 48)) = n := by
  subst h
  have : 1 < 10 := by decide
  by_cases hn : n = 0
  · simp_all
  · induction n using Nat.base_induction 10 this with
    | single m hm =>
      simp [Nat.toDigitsSane_of_lt hn hm]
      have := Nat.toNat_digitChar_of_lt_ten hm
      omega
    | digit m k hk hm ih =>
      rw [Nat.toDigitsSane_mul_add hm hk]
      simp [ih (Nat.pos_iff_ne_zero.1 hm)]
      have := Nat.toNat_digitChar_of_lt_ten hk
      omega

private theorem foldl_eq_iff_eq_toDigitsSane_map {l : List Char} {n : Nat}
    (hhead : ∀ c, l.head? = some c → c ≠ '0')
    (hdigit : ∀ c ∈ l, c.isDigit) :
    l.foldl (init := 0) (fun n c => n * 10 + (c.toNat - 48)) = n ↔
    l = (Nat.toDigitsSane 10 n (by decide)).map Nat.digitChar :=
  ⟨eq_toDigitsSane_map_of_foldl hhead hdigit, foldl_of_eq_toDigitsSane_map⟩

theorem List.foldl_ite_left {P : α → Prop} [DecidablePred P] {l : List α} {f : β → α → β} {init : β} :
    (l.foldl (init := init) fun sofar a => if P a then f sofar a else sofar) = (l.filter P).foldl (init := init) f := by
  simp [List.foldl_filter]

theorem List.foldl_ite_right {P : α → Prop} [DecidablePred P] {l : List α} {f : β → α → β} {init : β} :
    (l.foldl (init := init) fun sofar a => if P a then sofar else f sofar a) =
      (l.filter (fun a => ¬ P a)).foldl (init := init) f := by
  simp +singlePass only [← ite_not]
  rw [foldl_ite_left]

theorem bne_eq [BEq α] {a b : α} : (a != b) = !(a == b) := rfl

theorem toNat?_eq_some_iff {s : String.Slice} {n : Nat} :
    s.toNat? = some n ↔ s.isNat ∧
      (s.copy.toList.filter (· != '_')).dropWhile (· == '0') = (Nat.toDigitsSane 10 n (by decide)).map Nat.digitChar := by
  rw [toNat?]
  split <;> rename_i h
  · simp [h]
    rw [List.foldl_ite_right, foldl_dropWhile_zero]
    simp only [↓Char.isValue, decide_not, ← Bool.beq_eq_decide_eq, ← bne_eq]
    refine foldl_eq_iff_eq_toDigitsSane_map (fun c hc => ?_) (fun c hc => ?_)
    · simpa [hc] using List.head?_dropWhile_not (l := s.copy.toList.filter (· != '_')) (p := (· == '0'))
    · exact isDigit_of_isNat h _ (List.dropWhile_subset _ hc)
  · simp_all

end String.Slice

namespace Nat

private theorem toDigits_eq_toDigitsSane_map_digitChar {n : Nat} (hn : n ≠ 0) :
    Nat.toDigits 10 n = (Nat.toDigitsSane 10 n (by omega)).map Nat.digitChar := by
  induction n using Nat.strongRecOn with | ind n ih =>
  rw [toDigitsSane, dif_neg hn]
  by_cases hn' : n < 10
  · simp [Nat.div_eq_zero_iff.2 (Or.inr hn'), Nat.mod_eq_of_lt hn', toDigits_of_lt_base hn']
  · simp only [List.map_append, List.map_cons, List.map_nil]
    rw [toDigits_of_base_le (by omega) (by omega)]
    congr 1
    exact ih _ (Nat.div_lt_self (by omega) (by omega))
      (Nat.pos_iff_ne_zero.1 (Nat.div_pos (by omega) (by omega)))

private theorem head?_toDigits_ne_zero_char {n : Nat} (hn : n ≠ 0) :
    (Nat.toDigits 10 n).head? ≠ some '0' := by
  induction n using Nat.strongRecOn with | ind n ih =>
  by_cases hn' : n < 10
  · simp only [toDigits_of_lt_base hn', List.head?_cons, ne_eq, Option.some.injEq]
    intro h
    have h1 := toNat_digitChar_of_lt_ten hn'
    rw [h] at h1
    simp at h1
    omega
  · rw [toDigits_of_base_le (by omega) (by omega)]
    cases hl : Nat.toDigits 10 (n / 10) with
    | nil =>
      have := @length_toDigits_pos 10 (n / 10)
      simp [hl] at this
    | cons hd tl =>
      simp only [List.cons_append, List.head?_cons, ne_eq, Option.some.injEq]
      intro hc
      subst hc
      exact ih (n / 10) (Nat.div_lt_self (by omega) (by omega))
        (Nat.pos_iff_ne_zero.1 (Nat.div_pos (by omega) (by omega))) (by rw [hl]; simp)

theorem isNat_repr (n : Nat) : (Nat.repr n).toSlice.isNat = true := by
  apply String.Slice.isNat_of_isDigit
  · rw [String.isEmpty_toSlice, String.isEmpty_eq_false_iff]
    intro h
    have : 0 < (Nat.repr n).length := length_repr_pos
    rw [h] at this; simp at this
  · rw [String.copy_toSlice, repr_eq_ofList_toDigits, String.toList_ofList]
    exact fun c hc => isDigit_of_mem_toDigits (by omega) (by omega) hc

theorem repr_toSlice_toNat? (n : Nat) : (Nat.repr n).toSlice.toNat? = some n := by
  rw [String.Slice.toNat?_eq_some_iff]
  have hrw : (Nat.repr n).toSlice.copy.toList = Nat.toDigits 10 n := by
    rw [String.copy_toSlice, repr_eq_ofList_toDigits, String.toList_ofList]
  have hdigit : ∀ c ∈ Nat.toDigits 10 n, c.isDigit :=
    fun c hc => isDigit_of_mem_toDigits (by omega) (by omega) hc
  refine ⟨isNat_repr n, ?_⟩
  · rw [hrw]
    rw [List.filter_bne_eq_self_of_not_mem (fun h => absurd (hdigit _ h) (by decide))]
    by_cases hn : n = 0
    · subst hn; simp
    · rw [List.dropWhile_beq_eq_self_of_head?_ne (head?_toDigits_ne_zero_char hn)]
      exact toDigits_eq_toDigitsSane_map_digitChar hn

theorem repr_injective {m n : Nat} (h : Nat.repr m = Nat.repr n) : m = n := by
  have h1 := repr_toSlice_toNat? m
  have h2 := repr_toSlice_toNat? n
  rw [h] at h1
  exact Option.some.inj (h1.symm.trans h2)

end Nat

namespace String.Slice

theorem toNat?_map_repr_eq_some_self {s : String} :
    s.toSlice.toNat?.map Nat.repr = some s ↔ ∃ n, s = Nat.repr n := by
  constructor
  · intro h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨n, _, rfl⟩ := h
    exact ⟨n, rfl⟩
  · rintro ⟨n, rfl⟩
    simp [Nat.repr_toSlice_toNat?]

end String.Slice

namespace List

theorem mem_leftpad {n : Nat} {a c : α} {l : List α} (h : c ∈ l.leftpad n a) : c = a ∨ c ∈ l := by
  simp only [leftpad, mem_append, mem_replicate] at h
  exact h.elim (fun ⟨_, h⟩ => .inl h) .inr

private theorem leftpad_cons_self {n : Nat} {a : α} {l : List α} (h : l.length < n) :
    (a :: l).leftpad n a = l.leftpad n a := by
  simp only [leftpad, length_cons]
  rw [show a :: l = [a] ++ l from rfl, show [a] = replicate 1 a from rfl,
    ← append_assoc, replicate_append_replicate,
    show n - (l.length + 1) + 1 = n - l.length from by omega]

private theorem leftpad_append_singleton {n : Nat} {a x : α} {l : List α} (h : l.length ≤ n) :
    (l ++ [x]).leftpad (n + 1) a = l.leftpad n a ++ [x] := by
  simp only [leftpad, length_append, length_singleton, append_assoc]
  congr 1; congr 1; omega

end List

namespace Nat

theorem toDigits_pow_mul_add {k q r : Nat} (hq : 0 < q) (hr : r < 10 ^ k) (hk : 0 < k) :
    Nat.toDigits 10 (10 ^ k * q + r) =
      Nat.toDigits 10 q ++ (Nat.toDigits 10 r).leftpad k '0' := by
  sorry
  -- induction k with
  -- | zero => omega
  -- | succ k ih =>
  --   by_cases hk' : k = 0
  --   · -- k+1 = 1
  --     subst hk'; simp only [Nat.zero_add, Nat.pow_one] at *
  --     rw [← toDigits_append_toDigits (by omega) hq hr]
  --     congr 1; simp only [List.leftpad]
  --     have h1 := (length_toDigits_le_iff (by omega : (1 : Nat) < 10) (by omega : 0 < 1)).2 hr
  --     have h2 := @length_toDigits_pos 10 r
  --     simp [show 1 - (Nat.toDigits 10 r).length = 0 from by omega]
  --   · -- k ≥ 1
  --     have hk₁ : 0 < k := by omega
  --     have hge : 10 ≤ 10 ^ (k + 1) * q + r := by
  --       have h1 : 10 ≤ 10 ^ (k + 1) :=
  --         Nat.le_of_eq (by omega : 10 = 10 ^ 1) |>.trans (Nat.pow_le_pow_right (by omega) (by omega))
  --       have h2 : 10 ^ (k + 1) ≤ 10 ^ (k + 1) * q := Nat.le_mul_of_pos_right _ hq
  --       omega
  --     rw [toDigits_of_base_le (by omega) hge,
  --       show (10 ^ (k + 1) * q + r) / 10 = 10 ^ k * q + r / 10 from by
  --         rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_add_div (by omega)],
  --       show (10 ^ (k + 1) * q + r) % 10 = r % 10 from by
  --         rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_add_mod]]
  --     have hr' : r / 10 < 10 ^ k := by
  --       rw [Nat.pow_succ] at hr; exact (Nat.div_lt_iff_lt_mul (by omega)).2 hr
  --     rw [ih hq hr' hk₁, List.append_assoc]; congr 1
  --     rw [← List.leftpad_append_singleton ((length_toDigits_le_iff (by omega) hk₁).2 hr')]
  --     by_cases hr₁₀ : r < 10
  --     · simp only [Nat.div_eq_of_lt hr₁₀, Nat.mod_eq_of_lt hr₁₀,
  --         show Nat.toDigits 10 0 = ['0'] from rfl, List.singleton_append]
  --       rw [List.leftpad_cons_self (by simp; omega), toDigits_of_lt_base hr₁₀]
  --     · congr 1; exact (toDigits_of_base_le (by omega) (by omega)).symm

end Nat

namespace String.Slice

theorem isNat_append_underscore_append {s t : String}
    (hs : s.toSlice.isNat = true) (ht : t.toSlice.isNat = true) :
    (s ++ "_" ++ t).toSlice.isNat = true := by
  rw [isNat_iff] at hs ht ⊢
  obtain ⟨hse, hsc, hsi, hsh, hsl⟩ := hs
  obtain ⟨hte, htc, hti, hth, htl⟩ := ht
  simp only [String.copy_toSlice, String.toList_append, String.isEmpty_toSlice,
    String.reduceToList] at *
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- non-empty
    rw [String.isEmpty_eq_false_iff]; intro h
    have := congrArg String.toList h
    simp [String.toList_append, String.reduceToList] at this
  · -- all chars digit or _
    intro c hc
    simp only [List.mem_append, List.mem_singleton] at hc
    rcases hc with (hc | rfl) | hc
    · exact hsc c hc
    · exact Or.inr rfl
    · exact htc c hc
  · -- no consecutive underscores
    rw [show s.toList ++ ['_'] ++ t.toList = s.toList ++ ('_' :: t.toList) from by
      simp [List.append_assoc]]
    intro hinf
    rw [List.infix_iff_getElem?] at hinf
    obtain ⟨k, hlen, hk⟩ := hinf
    have hlen2 : (['_', '_'] : List Char).length = 2 := by decide
    simp only [hlen2, List.length_append, List.length_cons] at hlen
    have hk0 : (s.toList ++ ('_' :: t.toList))[k]? = some '_' := by
      have := hk 0 (by rw [hlen2]; omega)
      simp only [Nat.zero_add] at this; exact this
    have hk1 : (s.toList ++ ('_' :: t.toList))[k + 1]? = some '_' := by
      have := hk 1 (by rw [hlen2]; omega)
      simp only [show 1 + k = k + 1 from by omega] at this; exact this
    by_cases h1 : k + 2 ≤ s.toList.length
    · -- Both k and k+1 in s.toList
      rw [List.getElem?_append_left (by omega)] at hk0
      rw [List.getElem?_append_left (by omega)] at hk1
      exact hsi (List.infix_iff_getElem?.2 ⟨k, by rw [hlen2]; omega, fun i hi => by
        rw [hlen2] at hi
        match i with
        | 0 => simp only [Nat.zero_add]; exact hk0
        | 1 => simp only [show 1 + k = k + 1 from by omega]; exact hk1
        | n + 2 => omega⟩)
    · by_cases h2 : k + 1 ≤ s.toList.length
      · -- k is last of s.toList
        rw [List.getElem?_append_left (by omega)] at hk0
        rw [List.getLast?_eq_getElem?, show s.toList.length - 1 = k from by omega] at hsl
        exact hsl hk0
      · -- Both in '_' :: t.toList
        rw [List.getElem?_append_right (by omega)] at hk0 hk1
        by_cases h3 : k = s.toList.length
        · -- k at separator, k+1 first of t
          subst h3
          simp only [show s.toList.length + 1 - s.toList.length = 1 from by omega,
            List.getElem?_cons_succ] at hk1
          rw [List.head?_eq_getElem?] at hth
          exact hth hk1
        · -- Both in t.toList
          rw [show k - s.toList.length = (k - s.toList.length - 1) + 1 from by omega] at hk0
          rw [show k + 1 - s.toList.length = (k + 1 - s.toList.length - 1) + 1 from by omega] at hk1
          simp only [List.getElem?_cons_succ] at hk0 hk1
          exact hti (List.infix_iff_getElem?.2 ⟨k - s.toList.length - 1, by rw [hlen2]; omega,
            fun i hi => by
            rw [hlen2] at hi
            match i with
            | 0 => simp only [Nat.zero_add]; exact hk0
            | 1 =>
              simp only [show 1 + (k - s.toList.length - 1) = k + 1 - s.toList.length - 1
                from by omega]
              exact hk1
            | n + 2 => omega⟩)
  · -- no leading underscore
    cases hl : s.toList with
    | nil =>
      exact absurd (String.toList_eq_nil_iff.1 hl) (by rwa [String.isEmpty_eq_false_iff] at hse)
    | cons hd tl =>
      simp only [List.cons_append, List.head?_cons, ne_eq, Option.some.injEq]
      rw [hl] at hsh; simpa using hsh
  · -- no trailing underscore
    simp only [List.append_assoc, List.getLast?_append]
    cases h : t.toList.getLast? with
    | none =>
      exact absurd (String.toList_eq_nil_iff.1 (List.getLast?_eq_none_iff.1 h))
        (by rwa [String.isEmpty_eq_false_iff] at hte)
    | some c =>
      simp only [Option.some_or]; rw [← h]; exact htl

end String.Slice

def formatNum (n : Nat) : String :=
  if n < 1000 then Nat.repr n
  else formatNum (n / 1000) ++ "_" ++ .ofList ((Nat.toDigits 10 (n % 1000)).leftpad 3 '0')
termination_by n

private theorem filter_toList_formatNum (n : Nat) :
    (formatNum n).toList.filter (· != '_') = Nat.toDigits 10 n := by
  induction n using Nat.strongRecOn with | ind n ih =>
  unfold formatNum
  split
  · -- n < 1000
    rw [Nat.repr_eq_ofList_toDigits, String.toList_ofList, List.filter_eq_self]
    intro c hc; simp only [bne_iff_ne, ne_eq]; intro heq
    exact absurd (Nat.isDigit_of_mem_toDigits (by omega) (by omega) hc) (heq ▸ by decide)
  · -- n ≥ 1000
    rename_i h; replace h := Nat.not_lt.1 h
    simp only [String.toList_append, List.filter_append,
      String.reduceToList, String.toList_ofList,
      show (['_'] : List Char).filter (· != '_') = [] from by decide, List.append_nil]
    have hfilt : ((Nat.toDigits 10 (n % 1000)).leftpad 3 '0').filter (· != '_') =
        (Nat.toDigits 10 (n % 1000)).leftpad 3 '0' := by
      rw [List.filter_eq_self]
      intro c hc; simp only [bne_iff_ne, ne_eq]; intro heq
      rcases List.mem_leftpad hc with rfl | hc
      · exact absurd heq (by decide)
      · exact absurd (Nat.isDigit_of_mem_toDigits (by omega) (by omega) hc) (heq ▸ by decide)
    rw [hfilt, ih (n / 1000) (Nat.div_lt_self (by omega) (by omega))]
    have key := Nat.toDigits_pow_mul_add (show 0 < n / 1000 by omega) (Nat.mod_lt n (by omega))
      (show 0 < 3 by omega)
    simp only [show (10 : Nat) ^ 3 = 1000 from by decide] at key
    rw [Nat.div_add_mod n 1000] at key
    exact key.symm

private theorem isNat_formatNum (n : Nat) : (formatNum n).toSlice.isNat = true := by
  induction n using Nat.strongRecOn with | ind n ih =>
  unfold formatNum
  split
  · exact Nat.isNat_repr n
  · rename_i h; replace h := Nat.not_lt.1 h
    apply String.Slice.isNat_append_underscore_append
    · exact ih (n / 1000) (Nat.div_lt_self (by omega) (by omega))
    · apply String.Slice.isNat_of_isDigit
      · rw [String.isEmpty_toSlice, String.isEmpty_eq_false_iff]
        intro h
        have h1 : (Nat.toDigits 10 (n % 1000)).leftpad 3 '0' = [] := by
          have := congrArg String.toList h; rw [String.toList_ofList] at this; simpa using this
        simp only [List.leftpad, List.append_eq_nil_iff] at h1
        exact absurd h1.2 (by intro h; have := @Nat.length_toDigits_pos 10 (n % 1000); rw [h] at this; simp at this)
      · rw [String.copy_toSlice, String.toList_ofList]
        intro c hc
        rcases List.mem_leftpad hc with rfl | hc
        · decide
        · exact Nat.isDigit_of_mem_toDigits (by omega) (by omega) hc

theorem formatNum_toSlice_toNat? (n : Nat) : (formatNum n).toSlice.toNat? = some n := by
  rw [String.Slice.toNat?_eq_some_iff]
  refine ⟨isNat_formatNum n, ?_⟩
  rw [String.copy_toSlice, filter_toList_formatNum]
  by_cases hn : n = 0
  · subst hn; simp [show Nat.toDigits 10 0 = ['0'] from rfl]
  · rw [List.dropWhile_beq_eq_self_of_head?_ne (Nat.head?_toDigits_ne_zero_char hn)]
    exact Nat.toDigits_eq_toDigitsSane_map_digitChar hn
