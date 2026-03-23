/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.String.Slice
public import Init.Data.String.Search
public import Init.Data.Nat.ToString
import all Init.Data.String.Slice
import all Init.Data.String.Search
import Init.Data.String.Lemmas.Iterate
import Std.Tactic.Do
import Init.Data.List.Sublist

section NoRepetition

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
  simp only [noRepetition_iff, List.infix_concat_iff, not_or] at ⊢ h
  exact ⟨by rwa [← List.singleton_append, List.suffix_append_self_iff], h⟩

theorem NoRepetition.append_singleton_of_ne {α : Type u} {a b : α} {l : List α}
    (h : NoRepetition a l) (h' : a ≠ b) : NoRepetition a (l ++ [b]) := by
  simp only [noRepetition_iff, List.infix_concat_iff, not_or] at ⊢ h
  refine ⟨?_, h⟩
  rw [← List.singleton_append, List.suffix_append_inj_of_length_eq (by simp)]
  simp [h']

@[simp]
theorem noRepetition_singleton {α : Type u} {a b : α} : NoRepetition a [b] := by
  simpa [noRepetition_iff] using fun h => by simpa using h.length_le

theorem noRepetition_cons_append_append_iff {α : Type u} {a : α} {l : List α} :
    NoRepetition a (a :: (l ++ [a])) ↔
      l ≠ [] ∧ ¬ [a, a] <:+: l ∧ l.head? ≠ some a ∧ l.getLast? ≠ some a := by
  simp only [noRepetition_iff, List.infix_cons_iff, List.cons_prefix_cons, true_and,
    List.infix_concat_iff, not_or, ne_eq, ← List.singleton_prefix_iff_head?_eq_some,
    ← List.singleton_suffix_iff_getLast?_eq_some]
  conv => enter [1, 2]; rw [← List.singleton_append, List.suffix_append_self_iff]
  refine ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨?_, h₃, ?_, h₂⟩, fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨?_, h₄, h₂⟩⟩
  · rintro rfl
    simp_all
  · exact fun h => h₁ (List.prefix_append_of_prefix h)
  · cases l <;> simp_all

theorem noRepetition_append_cons_of_noRepetition_append_singleton {α : Type u} {a : α} {l m : List α}
    (h : NoRepetition a (l ++ [a])) (h' : NoRepetition a (a :: m)) : NoRepetition a (l ++ a :: m) := by
  simp [noRepetition_iff] at h h' ⊢
  simp [List.infix_append_iff_ne_nil]
  refine ⟨(h <| List.infix_append_of_infix_left ·), h',
    fun l₁ hl₁ l₂ hl₂ h₁ h₂ h₃ => h (List.IsSuffix.isInfix ?_)⟩
  obtain ⟨rfl, rfl⟩ : l₁ = [a] ∧ l₂ = [a] := by
    match l₁, hl₁, l₂, hl₂ with
    | [b], _, [c], _ =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true] at h₁
      obtain ⟨rfl, rfl⟩ := h₁
      simp
    | b::b'::bs, _, c::cs, _ => simp at h₁
  rwa [← List.singleton_append, List.suffix_append_self_iff]

end NoRepetition

namespace String.Slice

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

public theorem isNat_iff {s : String.Slice} :
    s.isNat = true ↔
      s.isEmpty = false ∧
      (∀ c ∈ s.copy.toList, c.isDigit ∨ c = '_') ∧
      ¬ ['_', '_'] <:+: s.copy.toList ∧
      s.copy.toList.head? ≠ some '_' ∧
      s.copy.toList.getLast? ≠ some '_' := by
  simp +contextual [isNat_iff', noRepetition_cons_append_append_iff]

public theorem isNat_of_isDigit {s : String.Slice} (hne : s.isEmpty = false)
    (hdigit : ∀ c ∈ s.copy.toList, c.isDigit) : s.isNat = true := by
  rw [isNat_iff]
  refine ⟨hne, fun c hc => Or.inl (hdigit c hc), fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := hdigit _ (by simpa using h.subset)
    simp at this
  · have := hdigit _ (s.copy.toList.mem_of_head? h)
    simp at this
  · have := hdigit _ (s.copy.toList.mem_of_getLast? h)
    simp at this

@[simp]
public theorem isSome_toNat? {s : String.Slice} : s.toNat?.isSome = s.isNat := by
  simp only [toNat?, ↓Char.isValue, Char.reduceToNat, foldl_eq_foldl_toList]
  split <;> simp_all

public theorem isNat_of_toNat?_eq_some {s : String.Slice} (h : s.toNat? = some n) : s.isNat = true := by
  simp [← isSome_toNat?, h]

@[simp]
public theorem toNat?_eq_none_iff {s : String.Slice} : s.toNat? = none ↔ s.isNat = false := by
  simp [← Option.isNone_iff_eq_none, ← Option.not_isSome, isSome_toNat?]

public theorem toNat?_eq_none {s : String.Slice} (h : s.isNat = false) : s.toNat? = none :=
  toNat?_eq_none_iff.2 h

public theorem toNat?_eq_some_ofDigitChars {s : String.Slice} (h : s.isNat = true) :
    s.toNat? = some (Nat.ofDigitChars 10 (s.copy.toList.filter (· != '_')) 0) := by
  rw [toNat?, if_pos h, Option.some.injEq]
  simp [Nat.ofDigitChars_eq_foldl, ↓Char.isValue, Char.reduceToNat, foldl_eq_foldl_toList, List.foldl_ite_right,
    bne_eq, Bool.beq_eq_decide_eq, Nat.mul_comm 10]

public theorem isNat_congr {s t : String.Slice} (h : s.copy = t.copy) : s.isNat = t.isNat := by
  rw [Bool.eq_iff_iff, isNat_iff, isNat_iff, ← isEmpty_copy]
  simp [h]

public theorem toNat?_congr {s t : String.Slice} (h : s.copy = t.copy) : s.toNat? = t.toNat? := by
  match h' : s.isNat with
  | false => rw [toNat?_eq_none h', toNat?_eq_none (isNat_congr h ▸ h')]
  | true => rw [toNat?_eq_some_ofDigitChars h', toNat?_eq_some_ofDigitChars (isNat_congr h ▸ h'), h]

end String.Slice

namespace String

@[simp]
public theorem isNat_toSlice {s : String} : s.toSlice.isNat = s.isNat :=
  (rfl)

@[simp]
public theorem isNat_comp_toSlice : String.Slice.isNat ∘ String.toSlice = String.isNat := by
  ext; simp

@[simp]
public theorem toNat?_toSlice {s : String} : s.toSlice.toNat? = s.toNat? :=
  (rfl)

@[simp]
public theorem toNat?_comp_toSlice : String.Slice.toNat? ∘ String.toSlice = String.toNat? := by
  ext; simp

@[simp]
public theorem Slice.isNat_copy {s : Slice} : s.copy.isNat = s.isNat := by
  simpa [← isNat_toSlice] using Slice.isNat_congr (by simp)

@[simp]
public theorem Slice.isNat_comp_copy : String.isNat ∘ String.Slice.copy = String.Slice.isNat := by
  ext; simp

@[simp]
public theorem Slice.toNat?_copy {s : Slice} : s.copy.toNat? = s.toNat? := by
  simpa [← isNat_toSlice] using Slice.toNat?_congr (by simp)

@[simp]
public theorem Slice.toNat?_comp_copy : String.toNat? ∘ String.Slice.copy = String.Slice.toNat? := by
  ext; simp

public theorem isNat_iff {s : String} :
    s.isNat = true ↔
      s ≠ "" ∧
      (∀ c ∈ s.toList, c.isDigit ∨ c = '_') ∧
      ¬ ['_', '_'] <:+: s.toList ∧
      s.toList.head? ≠ some '_' ∧
      s.toList.getLast? ≠ some '_' := by
  simp [← isNat_toSlice, Slice.isNat_iff]

public theorem isNat_of_isDigit {s : String} (hne : s ≠ "")
    (hdigit : ∀ c ∈ s.toList, c.isDigit) : s.isNat = true := by
  apply Slice.isNat_of_isDigit <;> simpa

@[simp]
public theorem isSome_toNat? {s : String} : s.toNat?.isSome = s.isNat := by
  simp [← isNat_toSlice, ← toNat?_toSlice]

public theorem isNat_of_toNat?_eq_some {s : String} (h : s.toNat? = some n) : s.isNat = true := by
  rw [← isNat_toSlice, Slice.isNat_of_toNat?_eq_some (by simpa)]

@[simp]
public theorem toNat?_eq_none_iff {s : String} : s.toNat? = none ↔ s.isNat = false := by
  simp [← isNat_toSlice, ← toNat?_toSlice]

public theorem toNat?_eq_none {s : String} (h : s.isNat = false) : s.toNat? = none :=
  toNat?_eq_none_iff.2 h

public theorem toNat?_eq_some_ofDigitChars {s : String} (h : s.isNat = true) :
    s.toNat? = some (Nat.ofDigitChars 10 (s.toList.filter (· != '_')) 0) := by
  rw [← toNat?_toSlice, Slice.toNat?_eq_some_ofDigitChars (by simpa), copy_toSlice]

public theorem isNat_append_underscore_append {s t : String}
    (hs : s.isNat = true) (ht : t.isNat = true) :
    (s ++ "_" ++ t).isNat = true := by
  rw [← isNat_toSlice, Slice.isNat_iff'] at hs ht ⊢
  simp only [copy_toSlice, ne_eq, toList_eq_nil_iff, ↓Char.isValue, List.cons_append, toList_append,
    String.reduceToList, List.append_assoc, List.nil_append, List.append_eq_nil_iff, reduceCtorEq,
    and_false, not_false_eq_true, List.mem_append, List.mem_cons, or_imp, imp_or_right_iff_true,
    true_and, forall_and] at hs ht ⊢
  refine ⟨⟨hs.2.1, ht.2.1⟩, ?_⟩
  have : '_' :: (s.toList ++ '_' :: (t.toList ++ ['_'])) =
    ('_' :: s.toList) ++ '_' :: (t.toList ++ ['_']) := by simp
  exact this ▸ noRepetition_append_cons_of_noRepetition_append_singleton hs.2.2 ht.2.2

public theorem toNat?_append_underscore_append_eq_some {s t : String} {n m : Nat}
    (hs : s.toNat? = some n) (ht : t.toNat? = some m) :
    (s ++ "_" ++ t).toNat? =
      some (10 ^ (t.toList.filter (· != '_')).length * n + m) := by
  rw [toNat?_eq_some_ofDigitChars (isNat_append_underscore_append
    (isNat_of_toNat?_eq_some hs) (isNat_of_toNat?_eq_some ht))]
  simp only [toNat?_eq_some_ofDigitChars (isNat_of_toNat?_eq_some hs),
    toNat?_eq_some_ofDigitChars (isNat_of_toNat?_eq_some ht), ↓Char.isValue,
    Option.some.injEq] at hs ht
  simp only [↓Char.isValue, toList_append, String.reduceToList, List.append_assoc, List.cons_append,
    List.nil_append, List.filter_append, bne_self_eq_false, Bool.false_eq_true, not_false_eq_true,
    List.filter_cons_of_neg, Nat.ofDigitChars_append, hs, Option.some.injEq]
  rw [Nat.ofDigitChars_eq_ofDigitChars_zero, ht]

end String

namespace Nat

@[simp]
public theorem isNat_repr (n : Nat) : (Nat.repr n).isNat = true := by
  apply String.isNat_of_isDigit (by simp)
  simpa using fun c hc => isDigit_of_mem_toDigits (by omega) (by omega) hc

@[simp]
public theorem toNat?_repr (n : Nat) : (Nat.repr n).toNat? = some n := by
  simp only [String.toNat?_eq_some_ofDigitChars (isNat_repr _), ↓Char.isValue, toList_repr,
    Option.some.injEq]
  rw [List.filter_bne_eq_self_of_not_mem (by simp)]
  simp

public theorem repr_injective {m n : Nat} (h : Nat.repr m = Nat.repr n) : m = n := by
  rw [← Option.some.injEq, ← toNat?_repr n, ← toNat?_repr m, h]

@[simp]
public theorem repr_inj {m n : Nat} : Nat.repr m = Nat.repr n ↔ m = n :=
  ⟨repr_injective, (· ▸ rfl)⟩

end Nat
