/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
prelude
import Init.Data.Char.Lemmas

namespace String

protected theorem data_eq_of_eq {a b : String} (h : a = b) : a.data = b.data :=
  h ▸ rfl
protected theorem ne_of_data_ne {a b : String} (h : a.data ≠ b.data) : a ≠ b :=
  fun h' => absurd (String.data_eq_of_eq h') h
@[simp] protected theorem lt_irrefl (s : String) : ¬ s < s :=
  List.lt_irrefl' Char.lt_irrefl s.data
protected theorem ne_of_lt {a b : String} (h : a < b) : a ≠ b := by
  have := String.lt_irrefl a
  intro h; subst h; contradiction

end String

namespace Char

@[simp] theorem length_toString (c : Char) : c.toString.length = 1 := rfl

end Char

namespace String


theorem ext {s₁ s₂ : String} (h : s₁.data = s₂.data) : s₁ = s₂ :=
  show ⟨s₁.data⟩ = (⟨s₂.data⟩ : String) from h ▸ rfl

theorem ext_iff {s₁ s₂ : String} : s₁ = s₂ ↔ s₁.data = s₂.data := ⟨fun h => h ▸ rfl, ext⟩

@[simp] theorem default_eq : default = "" := rfl

@[simp] theorem length_mk (s : List Char) : (String.mk s).length = s.length := rfl

@[simp] theorem length_empty : "".length = 0 := rfl

@[simp] theorem length_singleton (c : Char) : (String.singleton c).length = 1 := rfl

@[simp] theorem length_push (c : Char) : (String.push s c).length = s.length + 1 := by
  rw [push, length_mk, List.length_append, List.length_singleton, Nat.succ.injEq]
  rfl

@[simp] theorem length_pushn (c : Char) (n : Nat) : (pushn s c n).length = s.length + n := by
  unfold pushn; induction n <;> simp [Nat.repeat, Nat.add_assoc, *]

@[simp] theorem length_append (s t : String) : (s ++ t).length = s.length + t.length := by
  simp only [length, append, List.length_append]

@[simp] theorem data_push (s : String) (c : Char) : (s.push c).data = s.data ++ [c] := rfl

@[simp] theorem data_append (s t : String) : (s ++ t).data = s.data ++ t.data := rfl

attribute [simp] toList -- prefer `String.data` over `String.toList` in lemmas

theorem lt_iff (s t : String) : s < t ↔ s.data < t.data := .rfl

namespace Pos

@[simp] theorem byteIdx_zero : (0 : Pos).byteIdx = 0 := rfl

theorem byteIdx_mk (n : Nat) : byteIdx ⟨n⟩ = n := rfl

@[simp] theorem mk_zero : ⟨0⟩ = (0 : Pos) := rfl

@[simp] theorem mk_byteIdx (p : Pos) : ⟨p.byteIdx⟩ = p := rfl

theorem ext {i₁ i₂ : Pos} (h : i₁.byteIdx = i₂.byteIdx) : i₁ = i₂ :=
  show ⟨i₁.byteIdx⟩ = (⟨i₂.byteIdx⟩ : Pos) from h ▸ rfl

theorem ext_iff {i₁ i₂ : Pos} : i₁ = i₂ ↔ i₁.byteIdx = i₂.byteIdx := ⟨fun h => h ▸ rfl, ext⟩

@[simp] theorem add_byteIdx (p₁ p₂ : Pos) : (p₁ + p₂).byteIdx = p₁.byteIdx + p₂.byteIdx := rfl

theorem add_eq (p₁ p₂ : Pos) : p₁ + p₂ = ⟨p₁.byteIdx + p₂.byteIdx⟩ := rfl

@[simp] theorem sub_byteIdx (p₁ p₂ : Pos) : (p₁ - p₂).byteIdx = p₁.byteIdx - p₂.byteIdx := rfl

theorem sub_eq (p₁ p₂ : Pos) : p₁ - p₂ = ⟨p₁.byteIdx - p₂.byteIdx⟩ := rfl

@[simp] theorem addChar_byteIdx (p : Pos) (c : Char) : (p + c).byteIdx = p.byteIdx + csize c := rfl

theorem addChar_eq (p : Pos) (c : Char) : p + c = ⟨p.byteIdx + csize c⟩ := rfl

theorem zero_addChar_byteIdx (c : Char) : ((0 : Pos) + c).byteIdx = csize c := by
  simp only [addChar_byteIdx, byteIdx_zero, Nat.zero_add]

theorem zero_addChar_eq (c : Char) : (0 : Pos) + c = ⟨csize c⟩ := by rw [← zero_addChar_byteIdx]

theorem addChar_right_comm (p : Pos) (c₁ c₂ : Char) : p + c₁ + c₂ = p + c₂ + c₁ := by
  apply ext
  repeat rw [pos_add_char]
  apply Nat.add_right_comm

theorem ne_of_lt {i₁ i₂ : Pos} (h : i₁ < i₂) : i₁ ≠ i₂ := mt ext_iff.1 (Nat.ne_of_lt h)

theorem ne_of_gt {i₁ i₂ : Pos} (h : i₁ < i₂) : i₂ ≠ i₁ := (ne_of_lt h).symm

@[simp] theorem addString_byteIdx (p : Pos) (s : String) :
    (p + s).byteIdx = p.byteIdx + s.utf8ByteSize := rfl

theorem addString_eq (p : Pos) (s : String) : p + s = ⟨p.byteIdx + s.utf8ByteSize⟩ := rfl

theorem zero_addString_byteIdx (s : String) : ((0 : Pos) + s).byteIdx = s.utf8ByteSize := by
  simp only [addString_byteIdx, byteIdx_zero, Nat.zero_add]

theorem zero_addString_eq (s : String) : (0 : Pos) + s = ⟨s.utf8ByteSize⟩ := by
  rw [← zero_addString_byteIdx]

theorem le_iff {i₁ i₂ : Pos} : i₁ ≤ i₂ ↔ i₁.byteIdx ≤ i₂.byteIdx := .rfl

@[simp] theorem mk_le_mk {i₁ i₂ : Nat} : Pos.mk i₁ ≤ Pos.mk i₂ ↔ i₁ ≤ i₂ := .rfl

theorem lt_iff {i₁ i₂ : Pos} : i₁ < i₂ ↔ i₁.byteIdx < i₂.byteIdx := .rfl

@[simp] theorem mk_lt_mk {i₁ i₂ : Nat} : Pos.mk i₁ < Pos.mk i₂ ↔ i₁ < i₂ := .rfl

end Pos

--@[simp] theorem get!_eq_get (s : String) (p : Pos) : get! s p = get s p := rfl

theorem lt_next' (s : String) (p : Pos) : p < next s p := lt_next ..

@[simp] theorem prev_zero (s : String) : prev s 0 = 0 := rfl

@[simp] theorem get'_eq (s : String) (p : Pos) (h) : get' s p h = get s p := rfl

@[simp] theorem next'_eq (s : String) (p : Pos) (h) : next' s p h = next s p := rfl

-- `toSubstring'` is just a synonym for `toSubstring` without the `@[inline]` attribute
-- so for proving can be unfolded.
attribute [simp] toSubstring'

theorem singleton_eq (c : Char) : singleton c = ⟨[c]⟩ := rfl

@[simp] theorem data_singleton (c : Char) : (singleton c).data = [c] := rfl

@[simp] theorem append_empty (s : String) : s ++ "" = s := ext (List.append_nil _)

@[simp] theorem empty_append (s : String) : "" ++ s = s := rfl

theorem append_assoc (s₁ s₂ s₃ : String) : (s₁ ++ s₂) ++ s₃ = s₁ ++ (s₂ ++ s₃) :=
  ext (List.append_assoc ..)

end String

open String

namespace Substring

@[simp] theorem prev_zero (s : Substring) : s.prev 0 = 0 := by simp [prev, Pos.add_eq, Pos.byteIdx_zero]

@[simp] theorem prevn_zero (s : Substring) : ∀ n, s.prevn n 0 = 0
  | 0 => rfl
  | n+1 => by simp [prevn, prevn_zero s n]

end Substring
