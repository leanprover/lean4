/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel
-/
module

prelude
import Init.Data.List.Lemmas
import Init.Data.List.Basic
import Init.Data.List.Lex
import Init.Data.Order.Lemmas
import Init.Data.Order.LemmasExtra
import Init.Data.Nat.Order
import Init.Data.List.Sublist
import all Init.Data.String.Decode
import Init.Omega
import Init.Data.UInt.Lemmas
import Init.Data.String.Basic
import Init.Data.ByteArray.Lex
import Init.Data.Char.Order
import Init.ByCases
import Init.Data.Function
import Init.Data.BitVec.Package
import Init.Data.List.Package

namespace List

theorem nil_lt_iff [LT α] (l : List α) : [] < l ↔ l ≠ [] := by
  cases l <;> simp

theorem append_lt_append_iff_of_length_eq [LT α] (l₁ l₂ l₃ l₄ : List α) (h : l₁.length = l₂.length) :
    l₁ ++ l₃ < l₂ ++ l₄ ↔ l₁ < l₂ ∨ (l₁ = l₂ ∧ l₃ < l₄) := by
  induction l₁ generalizing l₂ with
  | nil =>
    simp only [length_nil, eq_comm, length_eq_zero_iff] at h
    simp [h]
  | cons a as ih =>
    cases l₂ with
    | nil => simp at h
    | cons b bs =>
      simp [List.cons_lt_cons_iff, ih bs (by simpa using h)]
      refine ⟨?_, ?_⟩
      · rintro (h|⟨rfl, (h₂|⟨rfl, h₂⟩)⟩) <;> simp_all
      · rintro ((h|⟨rfl, h⟩)|⟨⟨rfl, rfl⟩, h⟩) <;> simp_all

theorem compare_append_of_length_eq [Ord α] (l₁ l₂ l₃ l₄ : List α) (h : l₁.length = l₂.length) :
    compare (l₁ ++ l₃) (l₂ ++ l₄) = (compare l₁ l₂).then (compare l₃ l₄) := by
  induction l₁ generalizing l₂ with
  | nil =>
    simp only [length_nil, eq_comm, length_eq_zero_iff] at h
    simp [h]
  | cons a as ih =>
    cases l₂ with
    | nil => simp at h
    | cons b bs => simp [ih bs (by simpa using h), Ordering.then_assoc]

theorem append_le_append_iff_of_length_eq [LT α] [Std.Asymm (α := α) (· < ·)] [Std.Trichotomous (α := α) (· < ·)]  (l₁ l₂ l₃ l₄ : List α) (h : l₁.length = l₂.length) :
    l₁ ++ l₃ ≤ l₂ ++ l₄ ↔ l₁ < l₂ ∨ (l₁ = l₂ ∧ l₃ ≤ l₄) := by
  rw [← List.not_lt, append_lt_append_iff_of_length_eq _ _ _ _ h.symm, not_or, List.not_lt, not_and, List.not_lt]
  refine ⟨?_, ?_⟩
  · rintro ⟨h₁, h₂⟩
    obtain (h₁|rfl) := List.le_iff_lt_or_eq.1 h₁ <;> simp_all
  · rintro (h₁|⟨rfl, h₁⟩)
    · exact ⟨Std.le_of_lt h₁, by rintro rfl; simp [Std.lt_irrefl] at h₁⟩
    · simp_all

theorem append_right_lt_iff_of_length_eq [LT α] [Std.Irrefl (α := α) (· < ·)] (l₁ l₂ l₃ : List α) (h : l₁.length = l₂.length) : l₁ ++ l₃ < l₂ ++ l₃ ↔ l₁ < l₂ := by
  simp [append_lt_append_iff_of_length_eq _ _ _ _ h, Std.lt_irrefl]

@[simp]
theorem append_left_lt_iff [LT α] [Std.Irrefl (α := α) (· < ·)] (l₁ l₂ l₃ : List α) : l₁ ++ l₂ < l₁ ++ l₃ ↔ l₂ < l₃ := by
  simp [append_lt_append_iff_of_length_eq _ _ _ _ rfl, Std.lt_irrefl]

@[simp]
theorem append_left_le_iff [LT α] [Std.Asymm (α := α) (· < ·)] [Std.Trichotomous (α := α) (· < ·)] (l₁ l₂ l₃ : List α) : l₁ ++ l₂ ≤ l₁ ++ l₃ ↔ l₂ ≤ l₃ := by
  simp [append_le_append_iff_of_length_eq _ _ _ _ rfl, Std.lt_irrefl]

theorem cons_lt_cons_of_lt [LT α] {a b : α} {as bs : List α} : a < b → a :: as < b :: bs :=
  fun h => by simp [List.cons_lt_cons_iff, h]

theorem lt_of_getElem_zero [LT α] {as bs : List α} (h₁ h₂) (h : as[0]'h₁ < bs[0]'h₂) : as < bs :=
  List.lt_iff_exists.2 (Or.inr ⟨0, by simp_all⟩)

theorem lt_append_lt_of_not_prefix [LT α] (l₁ l₂ l₃ l₄ : List α) (h₁ : l₁ < l₂) (h₂ : ¬ l₁ <+: l₂) : l₁ ++ l₃ < l₂ ++ l₄ := by
  induction l₁ generalizing l₂ with
  | nil => simp_all
  | cons x xs ih =>
    cases l₂ with
    | nil => simp at h₁
    | cons y ys =>
      rw [List.cons_lt_cons_iff] at h₁
      rw [List.cons_append, List.cons_append, List.cons_lt_cons_iff]
      obtain (hxy|⟨rfl, hxy⟩) := h₁
      · exact Or.inl hxy
      · exact Or.inr ⟨rfl, ih _ hxy (by simpa using h₂)⟩

theorem flatMap_lt_flatMap_iff [LT α] [Std.Irrefl (α := α) (· < ·)] [Std.Trichotomous (α := α) (· < ·)] [LT β]
    [Std.Asymm (α := β) (· < ·)] [Std.Trichotomous (α := β) (· < ·)] (f : α → List β)
    (hf : ∀ a b, a < b → f a < f b)
    (hp : ∀ a b, f a <+: f b → a = b)
    (hx : ∀ a, f a ≠ [])
    (l l' : List α) :
    l.flatMap f < l'.flatMap f ↔ l < l' := by
  have hh {a b : α} {as bs : List α} (hab : a < b) : f a ++ as.flatMap f < f b ++ bs.flatMap f := by
    apply lt_append_lt_of_not_prefix
    · apply hf _ _ hab
    · intro h
      obtain rfl := hp _ _ h
      apply Std.lt_irrefl (a := a) hab
  classical
  induction l' generalizing l with
  | nil => simp
  | cons b bs ih =>
    cases l with
    | nil => simp [nil_lt_iff, hx b]
    | cons a as =>
      simp only [flatMap_cons, cons_lt_cons_iff, ← ih]
      refine ⟨?_, ?_⟩
      · rw [← Decidable.not_imp_not]
        simp only [not_or, not_and, List.not_lt, and_imp]
        rintro h₁ h₂
        obtain (hab|rfl|hab) := Std.lt_trichotomy a b
        · exact absurd hab h₁
        · apply append_left_le
          simp [h₂ rfl]
        · exact Std.le_of_lt (hh hab)
      · rintro (hab|⟨rfl, hab⟩)
        · exact hh hab
        · exact append_left_lt hab

/-- See `map_lt_map_iff` for a variant with fewer proof obligations for `f` but with some mild assumptions
on the order on `α` and `β`. -/
theorem map_lt_iff_of_injective [LT α] [LT β] (f : α → β) (hf : ∀ a b, a < b ↔ f a < f b) (hfinj : Function.Injective f) (l₁ l₂ : List α) :
    l₁.map f < l₂.map f ↔ l₁ < l₂ := by
  induction l₂ generalizing l₁ with
  | nil => simp
  | cons b bs ih =>
    cases l₁ with
    | nil => simp
    | cons a as => simp [List.cons_lt_cons_iff, ih, ← hf, hfinj.eq_iff]

/-- See `map_lt_map_iff_of_injective` for a variant which does not assume anything about the order on `α`
and `β`, but with more assumptions on `f`. -/
theorem map_lt_map_iff [LT α] [Std.Trichotomous (α := α) (· < ·)] [LT β] [Std.Asymm (α := β) (· < ·)] (f : α → β) (hf : ∀ a b, a < b → f a < f b) (l₁ l₂ : List α) :
    l₁.map f < l₂.map f ↔ l₁ < l₂ := by
  refine map_lt_iff_of_injective _ (fun a b => ⟨hf a b, fun hab => ?_⟩) (fun a b hab => ?_) _ _
  · obtain (h|rfl|h) := Std.lt_trichotomy a b
    · exact h
    · simp [Std.lt_irrefl] at hab
    · exact False.elim (absurd hab (Std.not_gt_of_lt (hf _ _ h)))
  · obtain (h|rfl|h) := Std.lt_trichotomy a b
    · exact False.elim (absurd hab (Std.ne_of_lt (hf _ _ h)))
    · rfl
    · exact False.elim (absurd hab.symm (Std.ne_of_lt (hf _ _ h)))

@[simp]
theorem toByteArray_lt_toByteArray {l₁ l₂ : List UInt8} : l₁.toByteArray < l₂.toByteArray ↔ l₁ < l₂ := by
  conv => rhs; rw [← List.toList_data_toByteArray (l := l₁), ← List.toList_data_toByteArray (l := l₂)]
  rw [Array.lt_toList, ByteArray.data_lt_data]

end List

namespace Nat

/-- To compare two two-digit numbers in base `m`, you first compare the most significant digit and
then compare the least significant digit. -/
theorem mul_add_lt_iff_of_lt {a b c d m : Nat} (hc : c < m) (hd : d < m) : a * m + c < b * m + d ↔ a < b ∨ (a = b ∧ c < d) := by
  refine ⟨?_, ?_⟩
  · rw [← Decidable.not_imp_not]
    simp only [not_or, Nat.not_lt, not_and, and_imp]
    intro h₁ h₂
    obtain (h₁|rfl) := Std.le_iff_lt_or_eq.1 h₁
    · apply Std.le_of_lt
      calc b * m + d < b * m + m := Nat.add_lt_add_left hd (b * m)
        _ = (b + 1) * m := (succ_mul b m).symm
        _ ≤ a * m := mul_le_mul_right m h₁
        _ ≤ a * m + c := le_add_right (a * m) c
    · exact Nat.add_le_add_iff_left.mpr (h₂ rfl)
  · rintro (h₁|⟨rfl, h₁⟩)
    · calc a * m + c < a * m + m := Nat.add_lt_add_left hc (a * m)
        _ = (a + 1) * m := (succ_mul a m).symm
        _ ≤ b * m := mul_le_mul_right m h₁
        _ ≤ b * m + d := le_add_right (b * m) d
    · exact Nat.add_lt_add_left h₁ (a * m)

end Nat

namespace Std

theorem eq_of_not_lt_of_not_gt [LT α] [Std.Trichotomous (α := α) (· < ·)] {a b : α} : ¬ a < b → ¬ b < a → a = b := by
  obtain (h|rfl|h) := Std.lt_trichotomy a b <;> simp [*]

theorem compare_eq_of_lt_iff [LE α] [LT α] [Std.Trichotomous (α := α) (· < ·)] [Std.LawfulOrderLT α] [Ord α] [Std.LawfulOrderOrd α] {a b : α} (o : Ordering) (h₁ : a < b ↔ o = .lt) (h₂ : b < a ↔ o = .gt) :
    compare a b = o := by
  cases o with
  | lt => simp_all [Std.compare_eq_lt]
  | eq =>
    rw [Std.compare_eq_eq_iff_eq]
    apply eq_of_not_lt_of_not_gt <;> simp_all
  | gt => simp_all [Std.compare_eq_gt]

end Std

namespace BitVec

theorem append_lt_append {w w' : Nat} (b₁ b₂ : BitVec w) (b₃ b₄ : BitVec w') : b₁ ++ b₃ < b₂ ++ b₄ ↔ b₁ < b₂ ∨ (b₁ = b₂ ∧ b₃ < b₄) := by
  simp only [lt_def, toNat_append, ← toNat_inj]
  rw [← Nat.shiftLeft_add_eq_or_of_lt b₃.isLt, ← Nat.shiftLeft_add_eq_or_of_lt b₄.isLt,
    Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.mul_add_lt_iff_of_lt b₃.isLt b₄.isLt]

theorem extractLsb'_eq_self' {w : Nat} (b : BitVec w) {len : Nat} (h : len = w) :
    b.extractLsb' 0 len = b.cast h.symm := by
  rw [← BitVec.extractLsb'_eq_self (x := b.cast h.symm), BitVec.extractLsb'_cast]

theorem eq_extractLsb'_append_extractLsb' {w : Nat} (b : BitVec w) (len : Nat) (h : len ≤ w) :
    b = (b.extractLsb' (w - len) len ++ b.extractLsb' 0 (w - len)).cast (by omega) := by
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by omega)]
  rw [BitVec.extractLsb'_eq_self' _ (by omega)]
  simp

@[simp]
theorem cast_lt_cast_iff {w w' : Nat} {h : w = w'} (b b' : BitVec w) : b.cast h < b'.cast h ↔ b < b' := by
  cases h; simp

theorem lt_of_lt_extractLsb {w : Nat} (b₁ b₂ : BitVec w) (len : Nat) (h : b₁.extractLsb' (w - len) len < b₂.extractLsb' (w - len) len) :
    b₁ < b₂ := by
  by_cases hlen : len ≤ w
  · rw [BitVec.eq_extractLsb'_append_extractLsb' b₁ len hlen,
      BitVec.eq_extractLsb'_append_extractLsb' b₂ len hlen]
    simp [BitVec.append_lt_append, h]
  · have : w - len = 0 := by omega
    simp only [this, lt_def, extractLsb'_toNat, Nat.shiftRight_zero] at h
    rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt] at h
    · simpa [BitVec.lt_def] using h
    · exact Std.lt_trans b₂.isLt (Nat.pow_lt_pow_right (by omega) (by omega))
    · exact Std.lt_trans b₁.isLt (Nat.pow_lt_pow_right (by omega) (by omega))

theorem compare_append_append {w w' : Nat} (b₁ b₂ : BitVec w) (b₃ b₄ : BitVec w') :
    @compare (no_index _) _ (@HAppend.hAppend _ _ _ _ b₁ b₃) (@HAppend.hAppend _ _ _ _ b₂ b₄) = (compare b₁ b₂).then (compare b₃ b₄) := by
  apply Std.compare_eq_of_lt_iff
  · simp [Ordering.then_eq_lt, Std.compare_eq_lt, append_lt_append]
  · simp [Ordering.then_eq_gt, Std.compare_eq_gt, append_lt_append, eq_comm (a := b₂)]

theorem setWidth_lt_setWidth_of_le {w w' : Nat} (b b' : BitVec w) (h : w ≤ w') :
    b.setWidth w' < b'.setWidth w' ↔ b < b' := by
  rw [BitVec.lt_def, BitVec.toNat_setWidth_of_le h, BitVec.toNat_setWidth_of_le h, BitVec.lt_def]

theorem compare_setWidth_setWidth_of_le {w w' : Nat} (b b' : BitVec w) (h : w ≤ w') :
    compare (b.setWidth w') (b'.setWidth w') = compare b b' := by
  apply Std.compare_eq_of_lt_iff <;> simp_all [setWidth_lt_setWidth_of_le, Std.compare_eq_lt, Std.compare_eq_gt]

end BitVec

theorem String.utf8EncodeChar_inj {c d : Char} (h : String.utf8EncodeChar c = String.utf8EncodeChar d) : c = d := by
  rw [← Option.some_inj, ← ByteArray.utf8DecodeChar?_utf8EncodeChar_append (b := ByteArray.empty),
    h, ByteArray.utf8DecodeChar?_utf8EncodeChar_append]

/-- UTF-8 is a prefix code: if `c` encodes to a prefix of `d`, then we must have `c = d`. -/
theorem String.eq_of_utf8EncodeChar_prefix {c d : Char} (h : String.utf8EncodeChar c <+: String.utf8EncodeChar d) : c = d := by
  suffices c.utf8Size = d.utf8Size from String.utf8EncodeChar_inj (h.eq_of_length
    (length_utf8EncodeChar c ▸ length_utf8EncodeChar d ▸ this))
  rw [← Char.utf8ByteSize_getElem_utf8EncodeChar]
  simp only [h.getElem, Char.utf8ByteSize_getElem_utf8EncodeChar]

theorem Char.utf8Size_le_of_le {c d : Char} (h : c ≤ d) : c.utf8Size ≤ d.utf8Size := by
  rw [Char.le_def, UInt32.le_iff_toNat_le] at h
  obtain (hc|hc|hc|hc) := c.utf8Size_eq <;> obtain (hd|hd|hd|hd) := d.utf8Size_eq <;> simp only [hc, hd]
  all_goals
    simp only [Char.utf8Size_eq_one_iff, Char.utf8Size_eq_two_iff, Char.utf8Size_eq_three_iff,
      Char.utf8Size_eq_four_iff, UInt32.le_iff_toNat_le, UInt32.lt_iff_toNat_lt, UInt32.reduceToNat] at hc hd
    omega

theorem helper {c d : Char} {w w' : Nat} (hw : w ≤ 8) (hw' : w' ≤ 8) {b : BitVec w} {a : BitVec (8 - w)} {b' : BitVec w'} {a' : BitVec (8 - w')}
    (h₁ : ((String.utf8EncodeChar c)[0]'(by simp [Char.utf8Size_pos])).toBitVec = (b ++ a).cast (by omega))
    (h₂ : ((String.utf8EncodeChar d)[0]'(by simp [Char.utf8Size_pos])).toBitVec = (b' ++ a').cast (by omega))
    (len : Nat) (hl₁ : len ≤ w := by omega) (hl₂ : len ≤ w' := by omega) (hlt : b.extractLsb' (w - len) len < b'.extractLsb' (w' - len) len := by simp)
    : String.utf8EncodeChar c < String.utf8EncodeChar d := by
  apply List.lt_of_getElem_zero (by simp [Char.utf8Size_pos]) (by simp [Char.utf8Size_pos])
  rw [UInt8.lt_iff_toBitVec_lt, h₁, h₂]
  apply BitVec.lt_of_lt_extractLsb _ _ len
  rwa [BitVec.extractLsb'_cast, BitVec.extractLsb'_cast, BitVec.extractLsb'_append_eq_of_le (by omega),
    BitVec.extractLsb'_append_eq_of_le (by omega), show 8 - len - (8 - w) = w - len by omega, show 8 - len - (8 - w') = w' - len by omega]

theorem String.utf8EncodeChar_lt_utf8EncodeChar_of_utf8Size_lt {c d : Char} (h : c.utf8Size < d.utf8Size) :
    String.utf8EncodeChar c < String.utf8EncodeChar d :=
  match hc : c.utf8Size, hd : d.utf8Size, c.utf8Size_pos, h, d.utf8Size_le_four with
  | 1, 2, _, _, _ => helper (by omega) (by omega)
      (String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_one hc)
      (String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_two hd) 1
  | 1, 3, _, _, _ => helper (by omega) (by omega)
      (String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_one hc)
      (String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_three hd) 1
  | 1, 4, _, _, _ => helper (by omega) (by omega)
      (String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_one hc)
      (String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_four hd) 1
  | 2, 3, _, _, _ => helper (by omega) (by omega)
      (String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_two hc)
      (String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_three hd) 3
  | 2, 4, _, _, _ => helper (by omega) (by omega)
      (String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_two hc)
      (String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_four hd) 3
  | 3, 4, _, _, _ => helper (by omega) (by omega)
      (String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_three hc)
      (String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_four hd) 4
  | n+4, _, _, _, _ => by omega

theorem Char.toBitVec_val_of_utf8Size_eq_one {c : Char} (hc : c.utf8Size = 1) :
    c.val.toBitVec = BitVec.setWidth 32 (BitVec.extractLsb' 0 7 c.val.toBitVec) := by
  rw [← BitVec.setWidth_eq_extractLsb' (by simp), BitVec.setWidth_setWidth_eq_self]
  simpa [BitVec.lt_def, UInt32.le_iff_toNat_le] using Nat.lt_succ_iff.2 (Char.utf8Size_eq_one_iff.1 hc)

theorem Char.toBitVec_val_of_utf8Size_eq_two {c : Char} (hc : c.utf8Size = 2) :
    c.val.toBitVec = BitVec.setWidth 32 (BitVec.extractLsb' 0 11 c.val.toBitVec) := by
  rw [← BitVec.setWidth_eq_extractLsb' (by simp), BitVec.setWidth_setWidth_eq_self]
  simpa [BitVec.lt_def, UInt32.le_iff_toNat_le] using Nat.lt_succ_iff.2 (Char.utf8Size_eq_two_iff.1 hc).2

theorem Char.toBitVec_val_of_utf8Size_eq_three {c : Char} (hc : c.utf8Size = 3) :
    c.val.toBitVec = BitVec.setWidth 32 (BitVec.extractLsb' 0 16 c.val.toBitVec) := by
  rw [← BitVec.setWidth_eq_extractLsb' (by simp), BitVec.setWidth_setWidth_eq_self]
  simpa [BitVec.lt_def, UInt32.le_iff_toNat_le] using Nat.lt_succ_iff.2 (Char.utf8Size_eq_three_iff.1 hc).2

theorem Char.toBitVec_val_of_utf8Size_eq_four {c : Char} (_hc : c.utf8Size = 4) :
    c.val.toBitVec = BitVec.setWidth 32 (BitVec.extractLsb' 0 21 c.val.toBitVec) := by
  rw [← BitVec.setWidth_eq_extractLsb' (by simp), BitVec.setWidth_setWidth_eq_self]
  have := c.toNat_le
  simp only [BitVec.lt_def, UInt32.toNat_toBitVec, BitVec.toNat_twoPow,
    Nat.reducePow, Nat.reduceMod, gt_iff_lt, Char.toNat_val]
  omega

theorem String.map_toBitVec_utf8EncodeChar_of_utf8Size_eq_one {c : Char} (h : c.utf8Size = 1) :
    (String.utf8EncodeChar c).map UInt8.toBitVec = [0#1 ++ c.val.toBitVec.extractLsb' 0 7] := by
  rw [List.eq_getElem_of_length_eq_one (String.utf8EncodeChar c) (length_utf8EncodeChar _ ▸ h),
    List.map_cons, List.map_nil, String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_one h]

theorem String.map_toBitVec_utf8EncodeChar_of_utf8Size_eq_two {c : Char} (h : c.utf8Size = 2) :
    (String.utf8EncodeChar c).map UInt8.toBitVec =
    [0b110#3 ++ c.val.toBitVec.extractLsb' 6 5,
     0b10#2 ++ c.val.toBitVec.extractLsb' 0 6] := by
  rw [List.eq_getElem_of_length_eq_two (String.utf8EncodeChar c) (length_utf8EncodeChar _ ▸ h),
    List.map_cons, List.map_cons, List.map_nil,
    String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_two h,
    String.toBitVec_getElem_utf8EncodeChar_one_of_utf8Size_eq_two h]

theorem String.map_toBitVec_utf8EncodeChar_of_utf8Size_eq_three {c : Char} (h : c.utf8Size = 3) :
    (String.utf8EncodeChar c).map UInt8.toBitVec =
    [0b1110#4 ++ c.val.toBitVec.extractLsb' 12 4,
     0b10#2 ++ c.val.toBitVec.extractLsb' 6 6,
     0b10#2 ++ c.val.toBitVec.extractLsb' 0 6] := by
  rw [List.eq_getElem_of_length_eq_three (String.utf8EncodeChar c) (length_utf8EncodeChar _ ▸ h),
    List.map_cons, List.map_cons, List.map_cons, List.map_nil,
    String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_three h,
    String.toBitVec_getElem_utf8EncodeChar_one_of_utf8Size_eq_three h,
    String.toBitVec_getElem_utf8EncodeChar_two_of_utf8Size_eq_three h]

theorem String.map_toBitVec_utf8EncodeChar_of_utf8Size_eq_four {c : Char} (h : c.utf8Size = 4) :
    (String.utf8EncodeChar c).map UInt8.toBitVec =
    [0b11110#5 ++ c.val.toBitVec.extractLsb' 18 3,
     0b10#2 ++ c.val.toBitVec.extractLsb' 12 6,
     0b10#2 ++ c.val.toBitVec.extractLsb' 6 6,
     0b10#2 ++ c.val.toBitVec.extractLsb' 0 6] := by
  rw [List.eq_getElem_of_length_eq_four (String.utf8EncodeChar c) (length_utf8EncodeChar _ ▸ h),
    List.map_cons, List.map_cons, List.map_cons, List.map_cons, List.map_nil,
    String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_four h,
    String.toBitVec_getElem_utf8EncodeChar_one_of_utf8Size_eq_four h,
    String.toBitVec_getElem_utf8EncodeChar_two_of_utf8Size_eq_four h,
    String.toBitVec_getElem_utf8EncodeChar_three_of_utf8Size_eq_four h]

theorem String.utf8EncodeChar_lt_utf8EncodeChar {c d : Char} (h : c < d) :
    String.utf8EncodeChar c < String.utf8EncodeChar d := by
  obtain (h₁|h₁) := Std.le_iff_lt_or_eq.1 (Char.utf8Size_le_of_le (Std.le_of_lt h))
  · exact String.utf8EncodeChar_lt_utf8EncodeChar_of_utf8Size_lt h₁
  · rw [← List.map_lt_map_iff UInt8.toBitVec (by simp [UInt8.lt_iff_toBitVec_lt]), ← Std.compare_eq_lt]
    rw [Char.lt_def, UInt32.lt_iff_toBitVec_lt, ← Std.compare_eq_lt] at h
    obtain (hc|hc|hc|hc) := c.utf8Size_eq <;> have hd := h₁ ▸ hc
    all_goals
      simp +singlePass (discharger := omega) only [
        Char.toBitVec_val_of_utf8Size_eq_one,
        Char.toBitVec_val_of_utf8Size_eq_two,
        Char.toBitVec_val_of_utf8Size_eq_three,
        Char.toBitVec_val_of_utf8Size_eq_four,
        BitVec.compare_setWidth_setWidth_of_le] at h
      simp (discharger := assumption) only [
        String.map_toBitVec_utf8EncodeChar_of_utf8Size_eq_one,
        String.map_toBitVec_utf8EncodeChar_of_utf8Size_eq_two,
        String.map_toBitVec_utf8EncodeChar_of_utf8Size_eq_three,
        String.map_toBitVec_utf8EncodeChar_of_utf8Size_eq_four,
        BitVec.compare_append_append,
        Nat.reduceAdd,
        List.compare_cons_cons,
        Std.compare_self,
        Ordering.eq_then,
        Ordering.then_eq]
      simpa (discharger := omega) only [← BitVec.compare_append_append,
        BitVec.extractLsb'_append_extractLsb'_eq_extractLsb']

theorem String.utf8EncodeChar_le_utf8EncodeChar {c d : Char} (h : c ≤ d) :
    String.utf8EncodeChar c ≤ String.utf8EncodeChar d := by
  obtain (h|rfl) := Std.le_iff_lt_or_eq.1 h
  · exact Std.le_of_lt (String.utf8EncodeChar_lt_utf8EncodeChar h)
  · exact Std.le_refl _

theorem String.lt_of_utf8EncodeChar_lt_utf8EncodeChar {c d : Char} (h : String.utf8EncodeChar c < String.utf8EncodeChar d) : c < d := by
  obtain (hc|rfl|hc) := Std.lt_trichotomy c d
  · exact hc
  · simp [Std.lt_irrefl] at h
  · exact False.elim (Std.not_gt_of_lt h (String.utf8EncodeChar_lt_utf8EncodeChar hc))

theorem String.toList_lt_iff_toByteArray_lt {s t : String} : s.toList < t.toList ↔ s.toByteArray < t.toByteArray := by
  obtain ⟨c, rfl⟩ := s.exists_eq_ofList
  obtain ⟨d, rfl⟩ := t.exists_eq_ofList
  simp [List.utf8Encode]
  rw [List.flatMap_lt_flatMap_iff]
  · exact fun a b => String.utf8EncodeChar_lt_utf8EncodeChar
  · exact fun a b => String.eq_of_utf8EncodeChar_prefix
  · simp
