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
import Init.Omega
import Init.Data.Int.Pow
import Init.Data.List.TakeDrop
import all Init.Data.Repr
import Init.Data.UInt.Lemmas
import Std.Tactic.Do
import Init.Data.String.Lemmas.FindPos
import Init.Data.List.Sublist
import Init.Data.List.Nat.Sublist

public section

theorem bne_eq [BEq α] {a b : α} : (a != b) = !(a == b) := rfl

namespace Nat

theorem toNat_digitChar_of_lt_ten {n : Nat} (hn : n < 10) : n.digitChar.toNat = 48 + n :=
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => by simp [digitChar]
  | _ + 10 => by omega

theorem toNat_digitChar_sub_48_of_lt_ten {n : Nat} (hn : n < 10) : n.digitChar.toNat - 48 = n := by
  simp [toNat_digitChar_of_lt_ten hn]

@[simp]
theorem Nat.digitChar_eq_zero_iff {n : Nat} : n.digitChar = '0' ↔ n = 0 :=
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | _ + 16 => by simp [digitChar]

def toDigitsSane (b : Nat) (n : Nat) (hb : 1 < b) : List Nat :=
  if h : n = 0 then
    []
  else
    have : n / b < n := Nat.div_lt_self (by omega) hb
    toDigitsSane b (n / b) hb ++ [n % b]

@[simp]
theorem toDigitsSane_zero {b : Nat} {hb : 1 < b} : toDigitsSane b 0 hb = [] := by
  simp [toDigitsSane]

@[simp]
theorem toDigitsSane_eq_nil_iff {b : Nat} {hb : 1 < b} {n : Nat} :
    toDigitsSane b n hb = [] ↔ n = 0 := by
  fun_induction toDigitsSane with simp_all

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

theorem prefix_iff_exists_append_eq {l₁ l₂ : List α} : l₁ <+: l₂ ↔ ∃ l₃, l₁ ++ l₃ = l₂ :=
  Iff.rfl

theorem prefix_iff_exists_eq_append {l₁ l₂ : List α} : l₁ <+: l₂ ↔ ∃ l₃, l₂ = l₁ ++ l₃ := by
  simp [prefix_iff_exists_append_eq, eq_comm]

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
  simp [prefix_iff_exists_eq_append, head?_eq_some_iff]

theorem infix_append_iff {α : Type u} {l m n : List α} : l <:+: m ++ n ↔
    l <:+: m ∨ l <:+: n ∨ (∃ l₁ l₂, l = l₁ ++ l₂ ∧ l₁ <:+ m ∧ l₂ <+: n) := by
  constructor
  · rintro ⟨s, t, ht⟩
    rcases List.append_eq_append_iff.mp ht with ⟨as, hm, _⟩ | ⟨bs, hsl, hn⟩
    · exact Or.inl ⟨s, as, hm.symm⟩
    · rcases List.append_eq_append_iff.mp hsl with ⟨cs, hm', hl⟩ | ⟨ds, _, hbs⟩
      · exact Or.inr (Or.inr ⟨cs, bs, hl,
          List.suffix_iff_exists_append.mpr ⟨s, hm'⟩,
          List.prefix_iff_exists_eq_append.mpr ⟨t, hn⟩⟩)
      · exact Or.inr (Or.inl ⟨ds, t, by rw [hn, ← hbs]⟩)
  · rintro (⟨s, t, ht⟩ | ⟨s, t, ht⟩ | ⟨l₁, l₂, rfl, hl₁, hl₂⟩)
    · exact ⟨s, t ++ n, by rw [← List.append_assoc, ht]⟩
    · exact ⟨m ++ s, t, by
        rw [List.append_assoc] at ht
        rw [List.append_assoc (m ++ s), List.append_assoc m, ht]⟩
    · rw [List.suffix_iff_exists_append] at hl₁
      rw [List.prefix_iff_exists_eq_append] at hl₂
      obtain ⟨s, hm⟩ := hl₁
      obtain ⟨t, hn⟩ := hl₂
      exact ⟨s, t, by rw [← List.append_assoc s l₁, List.append_assoc (s ++ l₁), hm, hn]⟩

theorem infix_append_iff_ne_nil {α : Type u} {l m n : List α} : l <:+: m ++ n ↔
    l <:+: m ∨ l <:+: n ∨ (∃ l₁ l₂, l₁ ≠ [] ∧ l₂ ≠ [] ∧ l = l₁ ++ l₂ ∧ l₁ <:+ m ∧ l₂ <+: n) := by
  rw [List.infix_append_iff]
  constructor
  · rintro (h | h | ⟨l₁, l₂, hl, hl₁, hl₂⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · by_cases h₁ : l₁ = []
      · subst h₁
        simp only [List.nil_append] at hl
        subst hl
        exact Or.inr (Or.inl hl₂.isInfix)
      · by_cases h₂ : l₂ = []
        · subst h₂
          simp only [List.append_nil] at hl
          subst hl
          exact Or.inl hl₁.isInfix
        · exact Or.inr (Or.inr ⟨l₁, l₂, h₁, h₂, hl, hl₁, hl₂⟩)
  · rintro (h | h | ⟨l₁, l₂, -, -, hl, hl₁, hl₂⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨l₁, l₂, hl, hl₁, hl₂⟩)

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

theorem foldl_ite_left {P : α → Prop} [DecidablePred P] {l : List α} {f : β → α → β} {init : β} :
    (l.foldl (init := init) fun sofar a => if P a then f sofar a else sofar) = (l.filter P).foldl (init := init) f := by
  simp [List.foldl_filter]

theorem foldl_ite_right {P : α → Prop} [DecidablePred P] {l : List α} {f : β → α → β} {init : β} :
    (l.foldl (init := init) fun sofar a => if P a then sofar else f sofar a) =
      (l.filter (fun a => ¬ P a)).foldl (init := init) f := by
  simp +singlePass only [← ite_not]
  rw [foldl_ite_left]

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

@[simp]
theorem isSome_toNat? {s : String.Slice} : s.toNat?.isSome = s.isNat := by
  simp only [toNat?, ↓Char.isValue, Char.reduceToNat, foldl_eq_foldl_toList]
  split <;> simp_all

theorem isNat_of_toNat?_eq_some {s : String.Slice} (h : s.toNat? = some n) : s.isNat = true := by
  simp [← isSome_toNat?, h]

def parseNat (l : List Char) (init : Nat) : Nat :=
  l.foldl (init := init) (fun sofar c => 10 * sofar + (c.toNat - '0'.toNat))

@[simp]
theorem parseNat_nil {init : Nat} : parseNat [] init = init := by
  simp [parseNat]

theorem parseNat_cons {c : Char} {cs : List Char} {init : Nat} :
    parseNat (c::cs) init = parseNat cs (10 * init + (c.toNat - '0'.toNat)) := by
  simp [parseNat]

theorem parseNat_cons_digitChar_of_lt_ten {n : Nat} (hn : n < 10) {cs : List Char} {init : Nat} :
    parseNat (n.digitChar :: cs) init = parseNat cs (10 * init + n) := by
  simp [parseNat_cons, Nat.toNat_digitChar_sub_48_of_lt_ten hn]

theorem parseNat_eq_parseNat_zero {l : List Char} {init : Nat} :
    parseNat l init = 10 ^ l.length * init + parseNat l 0 := by
  induction l generalizing init with
  | nil => simp [parseNat]
  | cons hd tl ih =>
    simp only [parseNat, ↓Char.isValue, Char.reduceToNat, List.foldl_cons, List.length_cons,
      Nat.mul_zero, Nat.zero_add] at ⊢ ih
    rw [ih, ih (init := hd.toNat - 48), Nat.pow_succ, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

theorem parseNat_append {l m : List Char} (init : Nat) :
    parseNat (l ++ m) init = parseNat m (parseNat l init) := by
  simp [parseNat]

theorem toNat?_eq_some_parseNat {s : String.Slice} (h : s.isNat = true) :
    s.toNat? = some (parseNat (s.copy.toList.filter (· != '_')) 0) := by
  rw [toNat?, if_pos h, Option.some.injEq]
  simp [parseNat, ↓Char.isValue, Char.reduceToNat, foldl_eq_foldl_toList, List.foldl_ite_right,
    bne_eq, Bool.beq_eq_decide_eq, Nat.mul_comm 10]

@[simp]
theorem parseNat_replicate_zero {n : Nat} : parseNat (List.replicate n '0') init = 10 ^ n * init := by
  induction n generalizing init with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, parseNat_cons, ih, Nat.pow_succ, Nat.mul_assoc]

@[simp]
theorem toNat?_eq_none_iff {s : String.Slice} : s.toNat? = none ↔ s.isNat = false := by
  simp [← Option.isNone_iff_eq_none, ← Option.not_isSome, isSome_toNat?]

theorem toNat?_eq_none {s : String.Slice} (h : s.isNat = false) : s.toNat? = none :=
  toNat?_eq_none_iff.2 h

end String.Slice

namespace Nat

theorem isNat_repr (n : Nat) : (Nat.repr n).toSlice.isNat = true := by
  apply String.Slice.isNat_of_isDigit
  · rw [String.isEmpty_toSlice, String.isEmpty_eq_false_iff]
    intro h
    have : 0 < (Nat.repr n).length := length_repr_pos
    rw [h] at this; simp at this
  · rw [String.copy_toSlice, repr_eq_ofList_toDigits, String.toList_ofList]
    exact fun c hc => isDigit_of_mem_toDigits (by omega) (by omega) hc

@[simp]
theorem Nat.toList_repr {n : Nat} : n.repr.toList = Nat.toDigits 10 n := by
  simp [Nat.repr]

@[simp]
theorem underscore_not_in_toDigits {n : Nat} : ¬'_' ∈ Nat.toDigits 10 n := by
  intro h
  simpa using isDigit_of_mem_toDigits (by decide) (by decide) h

@[simp]
theorem parseNat_toDigits {n : Nat} : String.Slice.parseNat (Nat.toDigits 10 n) 0 = n := by
  have : 1 < 10 := by decide
  induction n using base_induction 10 this with
  | single m hm =>
    simp [Nat.toDigits_of_lt_base hm, String.Slice.parseNat_cons_digitChar_of_lt_ten hm]
  | digit m k hk hm ih =>
    rw [← Nat.toDigits_append_toDigits this hm hk,
      String.Slice.parseNat_append, ih, Nat.toDigits_of_lt_base hk,
      String.Slice.parseNat_cons_digitChar_of_lt_ten hk, String.Slice.parseNat_nil]

@[simp]
theorem repr_toSlice_toNat? (n : Nat) : (Nat.repr n).toSlice.toNat? = some n := by
  simp [String.Slice.toNat?_eq_some_parseNat (isNat_repr _), Option.some.injEq]
  rw [List.filter_bne_eq_self_of_not_mem (by simp)]
  simp

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

end List

namespace String.Slice

theorem isNat_append_underscore_append {s t : String}
    (hs : s.toSlice.isNat = true) (ht : t.toSlice.isNat = true) :
    (s ++ "_" ++ t).toSlice.isNat = true := by
  rw [isNat_iff'] at hs ht ⊢
  simp only [copy_toSlice, ne_eq, toList_eq_nil_iff, ↓Char.isValue, List.cons_append, toList_append,
    String.reduceToList, List.append_assoc, List.nil_append, List.append_eq_nil_iff, reduceCtorEq,
    and_false, not_false_eq_true, List.mem_append, List.mem_cons, or_imp, imp_or_right_iff_true,
    true_and, forall_and] at hs ht ⊢
  refine ⟨⟨hs.2.1, ht.2.1⟩, ?_⟩
  have : '_' :: (s.toList ++ '_' :: (t.toList ++ ['_'])) =
    ('_' :: s.toList) ++ '_' :: (t.toList ++ ['_']) := by simp
  exact this ▸ noRepetition_append_cons_of_noRepetition_append_singleton hs.2.2 ht.2.2

theorem toNat?_append_underscore_append_eq_some {s t : String} {n m : Nat}
    (hs : s.toSlice.toNat? = some n) (ht : t.toSlice.toNat? = some m) :
    (s ++ "_" ++ t).toSlice.toNat? =
      some (10 ^ (t.toList.filter (· != '_')).length * n + m) := by
  rw [toNat?_eq_some_parseNat (isNat_append_underscore_append
    (isNat_of_toNat?_eq_some hs) (isNat_of_toNat?_eq_some ht))]
  simp [toNat?_eq_some_parseNat (isNat_of_toNat?_eq_some hs), Option.some.injEq] at hs
  simp [toNat?_eq_some_parseNat (isNat_of_toNat?_eq_some ht), Option.some.injEq] at ht
  simp [parseNat_append, hs]
  rw [parseNat_eq_parseNat_zero, ht]

end String.Slice

def formatNum (n : Nat) : String :=
  if n < 1000 then Nat.repr n
  else formatNum (n / 1000) ++ "_" ++ .ofList ((Nat.toDigits 10 (n % 1000)).leftpad 3 '0')
termination_by n

@[simp]
theorem toDigits_ne_nil {n b : Nat} : Nat.toDigits b n ≠ [] := by
  rw [← List.length_pos_iff]
  exact Nat.length_toDigits_pos

private theorem toNat?_ofList_leftpad3_toDigits (m : Nat) :
    (String.ofList ((Nat.toDigits 10 m).leftpad 3 '0')).toSlice.toNat? = some m := by
  rw [String.Slice.toNat?_eq_some_parseNat, Option.some.injEq, List.filter_bne_eq_self_of_not_mem (by simp)]
  · simp [String.Slice.parseNat_append]
  · apply String.Slice.isNat_of_isDigit
    · simp [← String.toList_inj]
    · simp only [List.leftpad, ↓Char.isValue, String.ofList_append, String.copy_toSlice,
        String.toList_append, String.toList_ofList, List.mem_append, List.mem_replicate, ne_eq]
      rintro c (⟨-, rfl⟩|hc)
      · simp
      · exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc

theorem formatNum_toSlice_toNat? (n : Nat) : (formatNum n).toSlice.toNat? = some n := by
  fun_induction formatNum with
  | case1 => simp
  | case2 n hn ih =>
    rw [String.Slice.toNat?_append_underscore_append_eq_some ih (toNat?_ofList_leftpad3_toDigits _),
      Option.some.injEq, List.filter_bne_eq_self_of_not_mem (by simp)]
    simp only [List.leftpad, ↓Char.isValue, String.ofList_append, String.toList_append,
      String.toList_ofList, List.length_append, List.length_replicate]
    rw [Nat.sub_add_cancel]
    · simpa using Nat.div_add_mod ..
    · rw [Nat.length_toDigits_le_iff (by decide) (by decide)]
      exact Nat.mod_lt _ (by decide)
