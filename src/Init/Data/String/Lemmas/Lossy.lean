/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel
-/
module

prelude
public import Init.Data.String.Lossy
import all Init.Data.String.Lossy
import all Init.Data.String.Decode
import Init.Data.String.Lemmas.Basic

namespace String

theorem skipContinuationBytes_le_size {b : ByteArray} {i : Nat} (hi : i ≤ b.size) :
    skipContinuationBytes b i ≤ b.size := by
  fun_induction skipContinuationBytes with
  | case1 i h₁ h₂ ih => exact ih (by omega)
  | case2 => exact hi
  | case3 => exact hi

theorem skipContinuationBytes_of_not_lt {b : ByteArray} {i : Nat} (h : ¬ i < b.size) :
    skipContinuationBytes b i = i := by
  rw [skipContinuationBytes, dite_eq_right h]

theorem skipContinuationBytes_of_isUTF8ContinuationByte {b : ByteArray} {i : Nat}
    (h : i < b.size) (hc : b[i].isUTF8ContinuationByte) :
    skipContinuationBytes b i = skipContinuationBytes b (i + 1) := by
  rw [skipContinuationBytes, dite_eq_left h, ite_eq_left hc]

theorem skipContinuationBytes_of_not_isUTF8ContinuationByte {b : ByteArray} {i : Nat}
    (h : i < b.size) (hc : ¬ b[i].isUTF8ContinuationByte) :
    skipContinuationBytes b i = i := by
  rw [skipContinuationBytes, dite_eq_left h, ite_eq_right hc]

theorem skipContinuationBytes_eq_of_forall_isUTF8ContinuationByte {b : ByteArray}
    {i j : Nat} (hij : i ≤ j) (hj : j ≤ b.size)
    (hcont : ∀ (k : Nat) (hk : k < b.size), i ≤ k → k < j → b[k].isUTF8ContinuationByte)
    (hstop : ∀ (h : j < b.size), ¬ b[j].isUTF8ContinuationByte) :
    skipContinuationBytes b i = j := by
  fun_induction skipContinuationBytes with
  | case1 i h₁ h₂ ih =>
    obtain (hij|rfl) := Nat.lt_or_eq_of_le hij
    · exact ih hij fun k hk hik hkj => hcont k hk (by omega) hkj
    · simp_all
  | case2 i h₁ h₂ =>
    suffices ¬ i < j by omega
    exact fun hlt => h₂ (hcont i h₁ (by omega) hlt)
  | case3 => omega

theorem skipContinuationBytes_extract {b : ByteArray} {i j : Nat} :
    i + skipContinuationBytes (b.extract i b.size) j = skipContinuationBytes b (i + j) := by
  fun_induction skipContinuationBytes (b.extract i b.size) j with
  | case1 j h₁ h₂ ih =>
    rw [ih, skipContinuationBytes_of_isUTF8ContinuationByte (b := b) (i := i + j)
      (by simp only [ByteArray.size_extract] at h₁; omega) (by simpa [ByteArray.getElem_extract] using h₂),
      Nat.add_assoc]
  | case2 j h₁ h₂ =>
    rw [skipContinuationBytes_of_not_isUTF8ContinuationByte (b := b) (i := i + j)
      (by simp only [ByteArray.size_extract] at h₁; omega) (by simpa [ByteArray.getElem_extract] using h₂)]
  | case3 j h₁ =>
    rw [skipContinuationBytes_of_not_lt (by simp only [ByteArray.size_extract] at h₁; omega)]

theorem skipContinuationBytes_eq_skipContinuationBytes_extract {b : ByteArray} {i : Nat} :
    skipContinuationBytes b i = i + skipContinuationBytes (b.extract i b.size) 0 := by
  simp [skipContinuationBytes_extract]

@[simp]
public theorem fromUTF8Lossy_empty : fromUTF8Lossy ByteArray.empty = "" := by
  simp [fromUTF8Lossy, fromUTF8Lossy.go]

theorem fromUTF8Lossy.go_of_not_lt {b : ByteArray} {i : Nat} {acc : String}
    (h : ¬ i < b.size) : fromUTF8Lossy.go b i acc = acc := by
  rw [fromUTF8Lossy.go, ite_eq_right h]

theorem fromUTF8Lossy.go_of_utf8DecodeChar?_eq_some {b : ByteArray} {i : Nat}
    {acc : String} {c : Char} (h : i < b.size)
    (hc : b.utf8DecodeChar? i = some c) :
    fromUTF8Lossy.go b i acc =
      fromUTF8Lossy.go b (i + c.utf8Size) (acc.push c) := by
  rw [fromUTF8Lossy.go, ite_eq_left h]
  split
  · rename_i d hd
    obtain rfl : c = d := by rw [← Option.some_inj, ← hc, hd]
    simp
  · simp_all

theorem fromUTF8Lossy.go_of_utf8DecodeChar?_eq_none {b : ByteArray} {i : Nat}
    {acc : String} (h : i < b.size) (hc : b.utf8DecodeChar? i = none) :
    fromUTF8Lossy.go b i acc =
      fromUTF8Lossy.go b (skipContinuationBytes b (i + 1)) (acc.push '\ufffd') := by
  rw [fromUTF8Lossy.go, ite_eq_left h]
  split
  · simp_all
  · rfl

theorem fromUTF8Lossy.go_eq_fromUTF8Lossy_extract {b : ByteArray} {i : Nat}
    {acc : String} : fromUTF8Lossy.go b i acc
      = acc ++ fromUTF8Lossy (b.extract i b.size) := by
  rw [fromUTF8Lossy]
  fun_cases fromUTF8Lossy.go b i acc with
  | case1 h c hc hpos =>
    rw [ByteArray.utf8DecodeChar?_eq_utf8DecodeChar?_extract] at hc
    conv => rhs; rw [fromUTF8Lossy.go_of_utf8DecodeChar?_eq_some (by simp; omega) hc]
    rw [fromUTF8Lossy.go_eq_fromUTF8Lossy_extract]
    conv => rhs; rw [fromUTF8Lossy.go_eq_fromUTF8Lossy_extract]
    simp [String.push_eq_append, -String.append_singleton, String.append_assoc,
      ByteArray.extract_extract, Nat.add_sub_cancel' (Nat.le_of_lt h)]
  | case2 h₁ hc h₃ =>
    rw [ByteArray.utf8DecodeChar?_eq_utf8DecodeChar?_extract] at hc
    conv => rhs; rw [fromUTF8Lossy.go_of_utf8DecodeChar?_eq_none (by simp; omega) hc]
    rw [fromUTF8Lossy.go_eq_fromUTF8Lossy_extract]
    have : b.size - i - (skipContinuationBytes (b.extract i b.size) 1) < b.size - i := by
      have := le_skipContinuationBytes (b.extract i b.size) 1
      omega
    conv => rhs; rw [fromUTF8Lossy.go_eq_fromUTF8Lossy_extract]
    rw [← String.append_assoc, String.push_eq_append (s := ""), String.empty_append,
      String.append_singleton]
    simp only [↓Char.isValue, ByteArray.size_extract, Std.min_self, ByteArray.extract_extract,
      Nat.add_sub_cancel' (Nat.le_of_lt h₁), append_right_inj]
    rw [skipContinuationBytes_eq_skipContinuationBytes_extract]
    conv => rhs; rw [skipContinuationBytes_eq_skipContinuationBytes_extract]
    simp [ByteArray.extract_extract, Nat.add_assoc, Nat.add_sub_cancel' (Nat.le_of_lt h₁)]
  | case3 h =>
    rw [fromUTF8Lossy.go_of_not_lt (by simp; omega), String.append_empty]
termination_by b.size - i

public theorem fromUTF8Lossy_of_utf8DecodeChar?_eq_some {b : ByteArray} {c : Char}
    (hc : b.utf8DecodeChar? 0 = some c) :
    fromUTF8Lossy b = String.singleton c ++ fromUTF8Lossy (b.extract c.utf8Size b.size) := by
  rw [fromUTF8Lossy, fromUTF8Lossy.go_of_utf8DecodeChar?_eq_some
    (ByteArray.lt_size_of_isSome_utf8DecodeChar? (by simp [hc])) hc,
    fromUTF8Lossy.go_eq_fromUTF8Lossy_extract, Nat.zero_add, String.singleton]

theorem fromUTF8Lossy_of_utf8DecodeChar?_eq_none {b : ByteArray} (h : 0 < b.size)
    (hc : b.utf8DecodeChar? 0 = none) :
    fromUTF8Lossy b =
      String.singleton '\ufffd' ++ fromUTF8Lossy (b.extract (skipContinuationBytes b 1) b.size) := by
  rw [fromUTF8Lossy, fromUTF8Lossy.go_of_utf8DecodeChar?_eq_none h hc,
    fromUTF8Lossy.go_eq_fromUTF8Lossy_extract, Nat.zero_add, singleton]

public theorem fromUTF8Lossy_utf8Encode_singleton_append {b : ByteArray} {c : Char} :
    fromUTF8Lossy ([c].utf8Encode ++ b) = String.singleton c ++ fromUTF8Lossy b := by
  rw [fromUTF8Lossy_of_utf8DecodeChar?_eq_some (c := c) (by simp),
    ByteArray.extract_append_eq_right _ (by simp)]
  simp [List.utf8Encode_singleton]

public theorem fromUTF8Lossy_utf8Encode_append {l : List Char} {b : ByteArray} :
    fromUTF8Lossy (l.utf8Encode ++ b) = String.ofList l ++ fromUTF8Lossy b := by
  induction l with
  | nil => simp
  | cons c cs ih =>
    rw [List.utf8Encode_cons, ByteArray.append_assoc,
      fromUTF8Lossy_utf8Encode_singleton_append, ih, String.ofList_cons,
      String.append_assoc]

@[simp]
public theorem fromUTF8Lossy_utf8Encode {l : List Char} :
    fromUTF8Lossy l.utf8Encode = String.ofList l := by
  simpa using fromUTF8Lossy_utf8Encode_append (l := l) (b := ByteArray.empty)

public theorem fromUTF8Lossy_eq_of_isValidUTF8 {b : ByteArray} (h : b.IsValidUTF8) :
    fromUTF8Lossy b = String.ofByteArray b h := by
  rcases h with ⟨l, rfl⟩
  simp [← String.toByteArray_inj]

@[simp]
public theorem fromUTF8Lossy_toByteArray {s : String} : fromUTF8Lossy s.toByteArray = s := by
  rw [← String.utf8Encode_toList, fromUTF8Lossy_utf8Encode, String.ofList_toList]

/--
If decoding `l ++ b` fails at the first byte, all other bytes of `l` are continuation bytes and `b`
does not start with a continuation byte, then `fromUTF8Lossy` replaces `l` with a single `�` and
continues with `b`.
-/
public theorem fromUTF8Lossy_append_of_utf8DecodeChar?_eq_none {l b : ByteArray}
    (hl : 0 < l.size) (h : (l ++ b).utf8DecodeChar? 0 = none)
    (hcont : ∀ (i : Nat) (hi : i < l.size), 0 < i → l[i].isUTF8ContinuationByte)
    (hb : ∀ (h : 0 < b.size), ¬ b[0].isUTF8ContinuationByte) :
    fromUTF8Lossy (l ++ b) = String.singleton '\ufffd' ++ fromUTF8Lossy b := by
  rw [fromUTF8Lossy_of_utf8DecodeChar?_eq_none (by simp only [ByteArray.size_append]; omega) h]
  have : skipContinuationBytes (l ++ b) 1 = l.size := by
    apply skipContinuationBytes_eq_of_forall_isUTF8ContinuationByte hl (by simp)
    · intro k hk h₁ h₂
      rw [ByteArray.getElem_append_left h₂]
      exact hcont k h₂ h₁
    · intro h'
      rw [ByteArray.getElem_append_right (Nat.le_refl _)]
      simpa using hb (by simp only [ByteArray.size_append] at h'; omega)
  rw [this, ByteArray.extract_append_eq_right rfl ByteArray.size_append]

/--
The bytes `0xED x y` with `0xA0 ≤ x < 0xC0` and `0x80 ≤ y < 0xC0` would encode a surrogate code
point (`U+D800` to `U+DFFF`), so `fromUTF8Lossy` replaces them with a single `�`, provided that `b`
does not start with a continuation byte.
-/
public theorem fromUTF8Lossy_surrogate_append {x y : UInt8} {b : ByteArray}
    (hx : 0xa0 ≤ x ∧ x < 0xc0) (hy : 0x80 ≤ y ∧ y < 0xc0)
    (hb : ∀ (h : 0 < b.size), ¬ b[0].isUTF8ContinuationByte) :
    String.fromUTF8Lossy ([0xed, x, y].toByteArray ++ b) =
      String.singleton '\ufffd' ++ String.fromUTF8Lossy b := by
  apply fromUTF8Lossy_append_of_utf8DecodeChar?_eq_none (by simp) _ _ hb
  · rw [utf8DecodeChar?_eq_assemble₃ (by simp) (by simp [ByteArray.utf8DecodeChar?.parseFirstByte])]
    clear hb
    simp only [List.size_toByteArray, List.length_cons, List.length_nil, Nat.zero_add,
      Nat.reduceAdd, Nat.zero_lt_succ, ByteArray.getElem_append_left, List.getElem_toByteArray,
      List.getElem_cons_zero, Nat.reduceLT, List.getElem_cons_succ, Nat.lt_add_one]
    suffices ∀ (x' : Nat), x' < 32 → ∀ (y' : Nat), y' < 64 →
        ByteArray.utf8DecodeChar?.assemble₃ 237 (UInt8.ofNat (160 + x')) (UInt8.ofNat (128 + y')) = none by
      simp only [UInt8.le_iff_toNat_le, UInt8.reduceToNat, UInt8.lt_iff_toNat_lt] at hx hy
      have hx' : UInt8.ofNat (160 + (x.toNat - 160)) = x := by simp [← UInt8.toNat_inj]; omega
      have hy' : UInt8.ofNat (128 + (y.toNat - 128)) = y := by simp [← UInt8.toNat_inj]; omega
      rw [← this (x.toNat - 160) (by omega) (y.toNat - 128) (by omega), hx', hy']
    decide +kernel
  · simp only [List.size_toByteArray, List.length_cons, List.length_nil, Nat.zero_add,
      Nat.reduceAdd, List.getElem_toByteArray]
    rintro (_|_|_|n)
    · simp
    · simp only [UInt8.le_iff_toNat_le, UInt8.reduceToNat, UInt8.lt_iff_toNat_lt, Nat.zero_add,
        Nat.reduceLT, Nat.lt_add_one, List.getElem_cons_succ, List.getElem_cons_zero,
        UInt8.isUTF8ContinuationByte_iff_le_and_lt, forall_const] at hx ⊢
      omega
    · simp only [UInt8.le_iff_toNat_le, UInt8.reduceToNat, UInt8.lt_iff_toNat_lt, Nat.zero_add,
        Nat.reduceAdd, Nat.lt_add_one, Nat.zero_lt_succ, List.getElem_cons_succ,
        List.getElem_cons_zero, UInt8.isUTF8ContinuationByte_iff_le_and_lt, forall_const] at hy ⊢
      omega
    · simp only [Nat.lt_add_left_iff_pos, Nat.zero_lt_succ, List.getElem_cons_succ, forall_const]
      omega

end String
