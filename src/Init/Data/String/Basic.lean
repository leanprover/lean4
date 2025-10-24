/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Mario Carneiro
-/
module

prelude
public import Init.Data.String.Decode
public import Init.Data.String.Defs
public import Init.Data.String.PosRaw
import Init.Data.ByteArray.Lemmas
import Init.Data.Char.Lemmas

/-!
# Strings

This file builds on the UTF-8 verification in `Init.Data.String.Decode` and the preliminary
material in `Init.Data.String.Defs` to get the theory of strings off the ground. In particular,
in this file we construct the decoding function `String.data : String → List Char` and show that
it is a two-sided inverse to `List.asString : List Char → String`. This in turn enables us to
understand the validity predicate on positions in terms of lists of characters, which forms the
basis for all further verification for strings.
-/

public section

universe u

section

@[simp]
theorem String.utf8ByteSize_singleton {c : Char} : (String.singleton c).utf8ByteSize = c.utf8Size := by
  simp [← size_bytes, List.utf8Encode_singleton]

theorem List.isUTF8FirstByte_getElem_utf8Encode_singleton {c : Char} {i : Nat} {hi : i < [c].utf8Encode.size} :
    UInt8.IsUTF8FirstByte [c].utf8Encode[i] ↔ i = 0 := by
  simp [List.utf8Encode_singleton, UInt8.isUTF8FirstByte_getElem_utf8EncodeChar]


theorem ByteArray.IsValidUTF8.push {b : ByteArray} (h : IsValidUTF8 b) {c : Char} (hc : c.utf8Size = 1) :
    IsValidUTF8 (b.push c.toUInt8) := by
  rcases h with ⟨m, rfl⟩
  refine ⟨m ++ [c], by simp [List.utf8Encode_singleton, String.utf8EncodeChar_eq_singleton hc]⟩

theorem ByteArray.isValidUTF8_utf8Encode_singleton_append_iff {b : ByteArray} {c : Char} :
    IsValidUTF8 ([c].utf8Encode ++ b) ↔ IsValidUTF8 b := by
  refine ⟨?_, fun h => IsValidUTF8.append isValidUTF8_utf8Encode h⟩
  rintro ⟨l, hl⟩
  match l with
  | [] => simp at hl
  | d::l =>
    obtain rfl : c = d := by
      replace hl := congrArg (fun l => utf8DecodeChar? l 0) hl
      simpa [List.utf8DecodeChar?_utf8Encode_singleton_append,
        List.utf8DecodeChar?_utf8Encode_cons] using hl
    rw [← List.singleton_append (l := l), List.utf8Encode_append,
      ByteArray.append_right_inj] at hl
    exact hl ▸ isValidUTF8_utf8Encode

/--
Decodes a sequence of characters from their UTF-8 representation. Returns `none` if the bytes are
not a sequence of Unicode scalar values.
-/
@[inline, expose]
def ByteArray.utf8Decode? (b : ByteArray) : Option (Array Char) :=
  go (b.size + 1) 0 #[] (by simp) (by simp)
where
  go (fuel : Nat) (i : Nat) (acc : Array Char) (hi : i ≤ b.size) (hf : b.size - i < fuel) : Option (Array Char) :=
    match fuel, hf with
    | fuel + 1, _ =>
      if i = b.size then
        some acc
      else
        match h : utf8DecodeChar? b i with
        | none => none
        | some c => go fuel (i + c.utf8Size) (acc.push c)
            (le_size_of_utf8DecodeChar?_eq_some h)
            (have := c.utf8Size_pos; have := le_size_of_utf8DecodeChar?_eq_some h; by omega)
  termination_by structural fuel

@[expose, extern "lean_string_validate_utf8"]
def ByteArray.validateUTF8 (b : ByteArray) : Bool :=
  go (b.size + 1) 0 (by simp) (by simp)
where
  go (fuel : Nat) (i : Nat) (hi : i ≤ b.size) (hf : b.size - i < fuel) : Bool :=
    match fuel, hf with
    | fuel + 1, _ =>
      if hi : i = b.size then
        true
      else
        match h : validateUTF8At b i with
        | false => false
        | true => go fuel (i + b[i].utf8ByteSize (isUTF8FirstByte_of_validateUTF8At h))
            ?_ ?_
  termination_by structural fuel
finally
  all_goals rw [ByteArray.validateUTF8At_eq_isSome_utf8DecodeChar?] at h
  · rw [← ByteArray.utf8Size_utf8DecodeChar (h := h)]
    exact add_utf8Size_utf8DecodeChar_le_size
  · rw [← ByteArray.utf8Size_utf8DecodeChar (h := h)]
    have := add_utf8Size_utf8DecodeChar_le_size (h := h)
    have := (b.utf8DecodeChar i h).utf8Size_pos
    omega

theorem ByteArray.isSome_utf8Decode?Go_eq_validateUTF8Go {b : ByteArray} {fuel : Nat}
    {i : Nat} {acc : Array Char} {hi : i ≤ b.size} {hf : b.size - i < fuel} :
    (utf8Decode?.go b fuel i acc hi hf).isSome = validateUTF8.go b fuel i hi hf := by
  fun_induction utf8Decode?.go with
  | case1 => simp [validateUTF8.go]
  | case2 i acc hi fuel hf h₁ h₂ =>
    simp only [Option.isSome_none, validateUTF8.go, h₁, ↓reduceDIte, Bool.false_eq]
    split
    · rfl
    · rename_i heq
      simp [validateUTF8At_eq_isSome_utf8DecodeChar?, h₂] at heq
  | case3 i acc hi fuel hf h₁ c h₂ ih =>
    simp [validateUTF8.go, h₁]
    split
    · rename_i heq
      simp [validateUTF8At_eq_isSome_utf8DecodeChar?, h₂] at heq
    · rw [ih]
      congr
      rw [← ByteArray.utf8Size_utf8DecodeChar (h := by simp [h₂])]
      simp [utf8DecodeChar, h₂]

theorem ByteArray.isSome_utf8Decode?_eq_validateUTF8 {b : ByteArray} :
    b.utf8Decode?.isSome = b.validateUTF8 :=
  b.isSome_utf8Decode?Go_eq_validateUTF8Go

theorem ByteArray.utf8Decode?.go.congr {b b' : ByteArray} {fuel fuel' i i' : Nat} {acc acc' : Array Char} {hi hi' hf hf'}
    (hbb' : b = b') (hii' : i = i') (hacc : acc = acc') :
    ByteArray.utf8Decode?.go b fuel i acc hi hf = ByteArray.utf8Decode?.go b' fuel' i' acc' hi' hf' := by
  subst hbb' hii' hacc
  fun_induction ByteArray.utf8Decode?.go b fuel i acc hi hf generalizing fuel' with
  | case1 =>
    rw [go.eq_def]
    split
    simp
  | case2 =>
    rw [go.eq_def]
    split <;> split
    · simp_all
    · split <;> simp_all
  | case3 =>
    conv => rhs; rw [go.eq_def]
    split <;> split
    · simp_all
    · split
      · simp_all
      · rename_i c₁ hc₁ ih _ _ _ _ _ c₂ hc₂
        obtain rfl : c₁ = c₂ := by rw [← Option.some_inj, ← hc₁, ← hc₂]
        apply ih

@[simp]
theorem ByteArray.utf8Decode?_empty : ByteArray.empty.utf8Decode? = some #[] := by
  simp [utf8Decode?, utf8Decode?.go]

private theorem ByteArray.isSome_utf8Decode?go_iff {b : ByteArray} {fuel i : Nat} {hi : i ≤ b.size} {hf} {acc : Array Char} :
    (ByteArray.utf8Decode?.go b fuel i acc hi hf).isSome ↔ IsValidUTF8 (b.extract i b.size) := by
  fun_induction ByteArray.utf8Decode?.go with
  | case1 => simp
  | case2 fuel i hi hf acc h₁ h₂ =>
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    rintro ⟨l, hl⟩
    have : l ≠ [] := by
      rintro rfl
      simp at hl
      omega
    rw [← l.cons_head_tail this] at hl
    rw [utf8DecodeChar?_eq_utf8DecodeChar?_extract, hl, List.utf8DecodeChar?_utf8Encode_cons] at h₂
    simp at h₂
  | case3 i acc hi fuel hf h₁ c h₂ ih =>
    rw [ih]
    have h₂' := h₂
    rw [utf8DecodeChar?_eq_utf8DecodeChar?_extract] at h₂'
    obtain ⟨l, hl⟩ := exists_of_utf8DecodeChar?_eq_some h₂'
    rw [ByteArray.extract_eq_extract_append_extract (i := i) (i + c.utf8Size) (by omega)
      (le_size_of_utf8DecodeChar?_eq_some h₂)] at hl ⊢
    rw [ByteArray.append_inj_left hl (by have := le_size_of_utf8DecodeChar?_eq_some h₂; simp; omega),
      ← List.utf8Encode_singleton, isValidUTF8_utf8Encode_singleton_append_iff]

theorem ByteArray.isSome_utf8Decode?_iff {b : ByteArray} :
    b.utf8Decode?.isSome ↔ IsValidUTF8 b := by
  rw [utf8Decode?, isSome_utf8Decode?go_iff, extract_zero_size]

@[simp]
theorem ByteArray.validateUTF8_eq_true_iff {b : ByteArray} :
    b.validateUTF8 = true ↔ IsValidUTF8 b := by
  rw [← isSome_utf8Decode?_eq_validateUTF8, isSome_utf8Decode?_iff]

@[simp]
theorem ByteArray.validateUTF8_eq_false_iff {b : ByteArray} :
    b.validateUTF8 = false ↔ ¬ IsValidUTF8 b := by
  simp [← Bool.not_eq_true]

instance {b : ByteArray} : Decidable b.IsValidUTF8 :=
  decidable_of_iff (b.validateUTF8 = true) ByteArray.validateUTF8_eq_true_iff

/--
Decodes an array of bytes that encode a string as [UTF-8](https://en.wikipedia.org/wiki/UTF-8) into
the corresponding string, or returns `none` if the array is not a valid UTF-8 encoding of a string.
-/
@[inline, expose] def String.fromUTF8? (a : ByteArray) : Option String :=
  if h : a.IsValidUTF8 then some (fromUTF8 a h) else none

/--
Decodes an array of bytes that encode a string as [UTF-8](https://en.wikipedia.org/wiki/UTF-8) into
the corresponding string, or panics if the array is not a valid UTF-8 encoding of a string.
-/
@[inline, expose] def String.fromUTF8! (a : ByteArray) : String :=
  if h : a.IsValidUTF8 then fromUTF8 a h else panic! "invalid UTF-8 string"

@[simp]
theorem String.empty_append {s : String} : "" ++ s = s := by
  simp [← String.bytes_inj]

@[simp]
theorem String.append_empty {s : String} : s ++ "" = s := by
  simp [← String.bytes_inj]

@[simp]
theorem List.asString_nil : List.asString [] = "" := by
  simp [← String.bytes_inj]

@[simp]
theorem List.asString_append {l₁ l₂ : List Char} : (l₁ ++ l₂).asString = l₁.asString ++ l₂.asString := by
  simp [← String.bytes_inj]

@[expose]
def String.Internal.toArray (b : String) : Array Char :=
  b.bytes.utf8Decode?.get (b.bytes.isSome_utf8Decode?_iff.2 b.isValidUTF8)

@[simp]
theorem String.Internal.toArray_empty : String.Internal.toArray "" = #[] := by
  simp [toArray]

@[extern "lean_string_data", expose]
def String.data (b : String) : List Char :=
  (String.Internal.toArray b).toList

@[simp]
theorem String.data_empty : "".data = [] := by
  simp [data]

/--
Returns the length of a string in Unicode code points.

Examples:
* `"".length = 0`
* `"abc".length = 3`
* `"L∃∀N".length = 4`
-/
@[extern "lean_string_length", expose]
def String.length (b : @& String) : Nat :=
  b.data.length

@[simp]
theorem String.Internal.size_toArray {b : String} : (String.Internal.toArray b).size = b.length :=
  (rfl)

@[simp]
theorem String.length_data {b : String} : b.data.length = b.length := (rfl)

private theorem ByteArray.utf8Decode?go_eq_utf8Decode?go_extract {b : ByteArray} {fuel i : Nat} {hi : i ≤ b.size} {hf} {acc : Array Char} :
    utf8Decode?.go b fuel i acc hi hf = (utf8Decode?.go (b.extract i b.size) fuel 0 #[] (by simp) (by simp [hf])).map (acc ++ ·) := by
  fun_cases utf8Decode?.go b fuel i acc hi hf with
  | case1 =>
      rw [utf8Decode?.go]
      simp only [size_extract, Nat.le_refl, Nat.min_eq_left, Nat.zero_add, List.push_toArray,
        List.nil_append]
      rw [if_pos (by omega)]
      simp
  | case2 fuel hf₁ h₁ h₂ hf₂ =>
    rw [utf8Decode?.go]
    simp only [size_extract, Nat.le_refl, Nat.min_eq_left, Nat.zero_add, List.push_toArray,
      List.nil_append]
    rw [if_neg (by omega)]
    rw [utf8DecodeChar?_eq_utf8DecodeChar?_extract] at h₂
    split <;> simp_all
  | case3 fuel hf₁ h₁ c h₂ hf₂ =>
    conv => rhs; rw [utf8Decode?.go]
    simp only [size_extract, Nat.le_refl, Nat.min_eq_left, Nat.zero_add, List.push_toArray,
      List.nil_append]
    rw [if_neg (by omega)]
    rw [utf8DecodeChar?_eq_utf8DecodeChar?_extract] at h₂
    split
    · simp_all
    · rename_i c' hc'
      obtain rfl : c = c' := by
        rw [← Option.some_inj, ← h₂, hc']
      have := c.utf8Size_pos
      conv => lhs; rw [ByteArray.utf8Decode?go_eq_utf8Decode?go_extract]
      conv => rhs; rw [ByteArray.utf8Decode?go_eq_utf8Decode?go_extract]
      simp only [size_extract, Nat.le_refl, Nat.min_eq_left, Option.map_map, ByteArray.extract_extract]
      have : (fun x => acc ++ x) ∘ (fun x => #[c] ++ x) = fun x => acc.push c ++ x := by funext; simp
      simp [(by omega : i + (b.size - i) = b.size), this]
termination_by fuel

theorem ByteArray.utf8Decode?_utf8Encode_singleton_append {l : ByteArray} {c : Char} :
    ([c].utf8Encode ++ l).utf8Decode? = l.utf8Decode?.map (#[c] ++ ·) := by
  rw [utf8Decode?, utf8Decode?.go,
    if_neg (by simp [List.utf8Encode_singleton]; have := c.utf8Size_pos; omega)]
  split
  · simp_all [List.utf8DecodeChar?_utf8Encode_singleton_append]
  · rename_i d h
    obtain rfl : c = d := by simpa [List.utf8DecodeChar?_utf8Encode_singleton_append] using h
    rw [utf8Decode?go_eq_utf8Decode?go_extract, utf8Decode?]
    simp only [List.push_toArray, List.nil_append, Nat.zero_add]
    congr 1
    apply ByteArray.utf8Decode?.go.congr _ rfl rfl
    apply extract_append_eq_right _ (by simp)
    simp [List.utf8Encode_singleton]

@[simp]
theorem List.utf8Decode?_utf8Encode {l : List Char} :
    l.utf8Encode.utf8Decode? = some l.toArray := by
  induction l with
  | nil => simp
  | cons c l ih =>
    rw [← List.singleton_append, List.utf8Encode_append]
    simp only [ByteArray.utf8Decode?_utf8Encode_singleton_append, cons_append, nil_append,
      Option.map_eq_some_iff, Array.append_eq_toArray_iff, cons.injEq, true_and]
    refine ⟨l.toArray, ih, by simp⟩

@[simp]
theorem ByteArray.utf8Encode_get_utf8Decode? {b : ByteArray} {h} :
    (b.utf8Decode?.get h).toList.utf8Encode = b := by
  obtain ⟨l, rfl⟩ := isSome_utf8Decode?_iff.1 h
  simp

@[simp]
theorem List.data_asString {l : List Char} : l.asString.data = l := by
  simp [String.data, String.Internal.toArray]

@[simp]
theorem String.asString_data {b : String} : b.data.asString = b := by
  obtain ⟨l, rfl⟩ := String.exists_eq_asString b
  rw [List.data_asString]

theorem List.asString_injective {l₁ l₂ : List Char} (h : l₁.asString = l₂.asString) : l₁ = l₂ := by
  simpa using congrArg String.data h

theorem List.asString_inj {l₁ l₂ : List Char} : l₁.asString = l₂.asString ↔ l₁ = l₂ :=
  ⟨asString_injective, (· ▸ rfl)⟩

theorem String.data_injective {s₁ s₂ : String} (h : s₁.data = s₂.data) : s₁ = s₂ := by
  simpa using congrArg List.asString h

theorem String.data_inj {s₁ s₂ : String} : s₁.data = s₂.data ↔ s₁ = s₂ :=
  ⟨data_injective, (· ▸ rfl)⟩

@[simp]
theorem String.data_append {l₁ l₂ : String} : (l₁ ++ l₂).data = l₁.data ++ l₂.data := by
  apply List.asString_injective
  simp

@[simp]
theorem String.utf8encode_data {b : String} : b.data.utf8Encode = b.bytes := by
  have := congrArg String.bytes (String.asString_data (b := b))
  rwa [← List.bytes_asString]

@[simp]
theorem String.data_eq_nil_iff {b : String} : b.data = [] ↔ b = "" := by
  rw [← List.asString_inj, asString_data, List.asString_nil]

@[simp]
theorem List.asString_eq_empty_iff {l : List Char} : l.asString = "" ↔ l = [] := by
  rw [← String.data_inj, List.data_asString, String.data_empty]

@[simp]
theorem List.length_asString {l : List Char} : l.asString.length = l.length := by
  rw [← String.length_data, List.data_asString]

end

namespace String

instance : LT String :=
  ⟨fun s₁ s₂ => s₁.data < s₂.data⟩

@[extern "lean_string_dec_lt"]
instance decidableLT (s₁ s₂ : @& String) : Decidable (s₁ < s₂) :=
  List.decidableLT s₁.data s₂.data

/--
Non-strict inequality on strings, typically used via the `≤` operator.

`a ≤ b` is defined to mean `¬ b < a`.
-/
@[expose, reducible] protected def le (a b : String) : Prop := ¬ b < a

instance : LE String :=
  ⟨String.le⟩

instance decLE (s₁ s₂ : String) : Decidable (s₁ ≤ s₂) :=
  inferInstanceAs (Decidable (Not _))

/--
Converts a string to a list of characters.

Since strings are represented as dynamic arrays of bytes containing the string encoded using
UTF-8, this operation takes time and space linear in the length of the string.

Examples:
 * `"abc".toList = ['a', 'b', 'c']`
 * `"".toList = []`
 * `"\n".toList = ['\n']`
-/
@[inline, expose]
def toList (s : String) : List Char :=
  s.data

theorem _root_.List.isPrefix_of_utf8Encode_append_eq_utf8Encode {l m : List Char} (b : ByteArray)
    (h : l.utf8Encode ++ b = m.utf8Encode) : l <+: m := by
  induction l generalizing m with
  | nil => simp
  | cons c l ih =>
    replace h := congrArg ByteArray.utf8Decode? h
    rw [List.utf8Decode?_utf8Encode] at h
    rw [← List.singleton_append, List.utf8Encode_append, ByteArray.append_assoc,
      ByteArray.utf8Decode?_utf8Encode_singleton_append] at h
    suffices ∃ m', m = [c] ++ m' ∧ l.utf8Encode ++ b = m'.utf8Encode by
      obtain ⟨m', rfl, hm'⟩ := this
      simpa using ih hm'
    have hx : (l.utf8Encode ++ b).utf8Decode?.isSome := by
      exact Option.isSome_map ▸ Option.isSome_of_eq_some h
    refine ⟨(l.utf8Encode ++ b).utf8Decode?.get hx |>.toList, ?_, by simp⟩
    exact List.toArray_inj (Option.some_inj.1 (by simp [← h]))

open List in
theorem Pos.Raw.IsValid.exists {s : String} {p : Pos.Raw} (h : p.IsValid s) :
    ∃ m₁ m₂ : List Char, m₁.utf8Encode = s.bytes.extract 0 p.byteIdx ∧ (m₁ ++ m₂).asString = s := by
  obtain ⟨l, hl⟩ := s.isValidUTF8
  obtain ⟨m₁, hm₁⟩ := h.isValidUTF8_extract_zero
  suffices m₁ <+: l by
    obtain ⟨m₂, rfl⟩ := this
    refine ⟨m₁, m₂, hm₁.symm, ?_⟩
    apply String.bytes_inj.1
    simpa using hl.symm
  apply List.isPrefix_of_utf8Encode_append_eq_utf8Encode (s.bytes.extract p.byteIdx s.bytes.size)
  rw [← hl, ← hm₁, ← ByteArray.extract_eq_extract_append_extract _ (by simp),
    ByteArray.extract_zero_size]
  simpa using h.le_rawEndPos

theorem Pos.Raw.IsValid.isValidUTF8_extract_utf8ByteSize {s : String} {p : Pos.Raw} (h : p.IsValid s) :
    ByteArray.IsValidUTF8 (s.bytes.extract p.byteIdx s.utf8ByteSize) := by
  obtain ⟨m₁, m₂, hm, rfl⟩ := h.exists
  simp only [List.asString_append, bytes_append, List.bytes_asString]
  rw [ByteArray.extract_append_eq_right]
  · exact ByteArray.isValidUTF8_utf8Encode
  · rw [hm]
    simp only [List.asString_append, bytes_append, List.bytes_asString, ByteArray.size_extract,
      ByteArray.size_append, Nat.sub_zero]
    refine (Nat.min_eq_left ?_).symm
    simpa [utf8ByteSize, Pos.Raw.le_iff] using h.le_rawEndPos
  · simp [utf8ByteSize]

theorem Pos.Raw.isValid_iff_exists_append {s : String} {p : Pos.Raw} :
    p.IsValid s ↔ ∃ s₁ s₂ : String, s = s₁ ++ s₂ ∧ p = s₁.rawEndPos := by
  refine ⟨fun h => ⟨⟨_, h.isValidUTF8_extract_zero⟩, ⟨_, h.isValidUTF8_extract_utf8ByteSize⟩, ?_, ?_⟩, ?_⟩
  · apply String.bytes_inj.1
    have := Pos.Raw.le_iff.1 h.le_rawEndPos
    simp_all [← size_bytes]
  · have := byteIdx_rawEndPos ▸ Pos.Raw.le_iff.1 h.le_rawEndPos
    apply String.Pos.Raw.ext
    simp [Nat.min_eq_left this]
  · rintro ⟨s₁, s₂, rfl, rfl⟩
    refine isValid_iff_isValidUTF8_extract_zero.2 ⟨by simp [Pos.Raw.le_iff], ?_⟩
    simpa [ByteArray.extract_append_eq_left] using s₁.isValidUTF8

theorem Pos.Raw.isValid_asString {l : List Char} {p : Pos.Raw} :
    p.IsValid l.asString ↔ ∃ i, p.byteIdx = (l.take i).asString.utf8ByteSize := by
  rw [isValid_iff_exists_append]
  refine ⟨?_, ?_⟩
  · rintro ⟨t₁, t₂, ht, rfl⟩
    refine ⟨t₁.length, ?_⟩
    have := congrArg String.data ht
    simp only [List.data_asString, String.data_append] at this
    simp [this]
  · rintro ⟨i, hi⟩
    refine ⟨(l.take i).asString, (l.drop i).asString, ?_, ?_⟩
    · simp [← List.asString_append]
    · simpa [Pos.Raw.ext_iff]

theorem Pos.Raw.isValid_iff_exists_take_data {s : String} {p : Pos.Raw} :
    p.IsValid s ↔ ∃ i, p.byteIdx = (s.data.take i).asString.utf8ByteSize := by
  obtain ⟨l, rfl⟩ := s.exists_eq_asString
  simp [isValid_asString]

@[simp]
theorem Pos.Raw.isValid_singleton {c : Char} {p : Pos.Raw} :
    p.IsValid (String.singleton c) ↔ p = 0 ∨ p.byteIdx = c.utf8Size := by
  rw [singleton_eq_asString, Pos.Raw.isValid_asString]
  refine ⟨?_, ?_⟩
  · rintro ⟨i, hi'⟩
    obtain ⟨rfl, hi⟩ : i = 0 ∨ 1 ≤ i := by omega
    · simp [Pos.Raw.ext_iff, hi']
    · rw [hi', List.take_of_length_le (by simpa)]
      simp [← singleton_eq_asString]
  · rintro (rfl|hi)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp [hi, ← singleton_eq_asString]⟩

theorem Pos.Raw.isValid_append {s t : String} {p : Pos.Raw} :
    p.IsValid (s ++ t) ↔ p.IsValid s ∨ (s.rawEndPos ≤ p ∧ (p - s).IsValid t) := by
  obtain ⟨s, rfl⟩ := exists_eq_asString s
  obtain ⟨t, rfl⟩ := exists_eq_asString t
  rw [← List.asString_append, Pos.Raw.isValid_asString, Pos.Raw.isValid_asString, Pos.Raw.isValid_asString]
  refine ⟨?_, ?_⟩
  · rintro ⟨j, hj⟩
    by_cases h : j ≤ s.length
    · exact Or.inl ⟨j, by simp [hj, List.take_append_of_le_length h]⟩
    · refine Or.inr ⟨?_, ⟨j - s.length, ?_⟩⟩
      · simp [Pos.Raw.le_iff, hj, List.take_append, List.take_of_length_le (i := j) (l := s) (by omega)]
      · simp [hj, List.take_append, List.take_of_length_le (i := j) (l := s) (by omega)]
  · rintro (⟨j, hj⟩|⟨h, ⟨j, hj⟩⟩)
    · refine ⟨min j s.length, ?_⟩
      rw [List.take_append_of_le_length (Nat.min_le_right ..), ← List.take_eq_take_min, hj]
    · refine ⟨s.length + j, ?_⟩
      simp only [Pos.Raw.byteIdx_sub_string, byteIdx_rawEndPos, Pos.Raw.le_iff] at hj h
      simp only [List.take_append, List.take_of_length_le (i := s.length + j) (l := s) (by omega),
        Nat.add_sub_cancel_left, List.asString_append, utf8ByteSize_append]
      omega

theorem Pos.Raw.IsValid.append_left {t : String} {p : Pos.Raw} (h : p.IsValid t) (s : String) :
    (s + p).IsValid (s ++ t) :=
  isValid_append.2 (Or.inr ⟨by simp [Pos.Raw.le_iff], by
    suffices p = s + p - s by simp [← this, h]
    simp [Pos.Raw.ext_iff]⟩)

theorem Pos.Raw.IsValid.append_right {s : String} {p : Pos.Raw} (h : p.IsValid s) (t : String) :
    p.IsValid (s ++ t) :=
  isValid_append.2 (Or.inl h)

theorem Pos.Raw.isValid_push {s : String} {c : Char} {p : Pos.Raw} :
    p.IsValid (s.push c) ↔ p.IsValid s ∨ p = s.rawEndPos + c := by
  rw [← append_singleton, isValid_append, isValid_singleton]
  simp only [le_iff, byteIdx_rawEndPos, Pos.Raw.ext_iff, byteIdx_sub_string, byteIdx_zero, byteIdx_add_char]
  refine ⟨?_, ?_⟩
  · rintro (h|⟨h₁,(h₂|h₂)⟩)
    · exact Or.inl h
    · suffices p = s.rawEndPos by simp [this]
      simp only [Pos.Raw.ext_iff, byteIdx_rawEndPos]
      omega
    · omega
  · rintro (h|h)
    · exact Or.inl h
    · omega

@[simp]
theorem utf8ByteSize_push {s : String} {c : Char} :
    (s.push c).utf8ByteSize = s.utf8ByteSize + c.utf8Size := by
  simp [← size_bytes, List.utf8Encode_singleton]

theorem rawEndPos_push {s : String} {c : Char} : (s.push c).rawEndPos = s.rawEndPos + c := by
  simp [Pos.Raw.ext_iff]

@[deprecated rawEndPos_push (since := "2025-10-20")]
theorem endPos_push {s : String} {c : Char} : (s.push c).rawEndPos = s.rawEndPos + c :=
  rawEndPos_push

theorem push_induction (s : String) (motive : String → Prop) (empty : motive "")
    (push : ∀ b c, motive b → motive (b.push c)) : motive s := by
  obtain ⟨m, rfl⟩ := s.exists_eq_asString
  apply append_singleton_induction m (motive ·.asString)
  · simpa
  · intro l c hl
    rw [List.asString_append, ← singleton_eq_asString, append_singleton]
    exact push _ _ hl
where
  append_singleton_induction (l : List Char) (motive : List Char → Prop) (nil : motive [])
      (append_singleton : ∀ l a, motive l → motive (l ++ [a])) : motive l := by
    rw [← l.reverse_reverse]
    generalize l.reverse = m
    induction m with
    | nil => simpa
    | cons a m ih =>
      rw [List.reverse_cons]
      exact append_singleton _ _ ih

theorem Pos.Raw.isValid_iff_isUTF8FirstByte {s : String} {p : Pos.Raw} :
    p.IsValid s ↔ p = s.rawEndPos ∨ ∃ (h : p < s.rawEndPos), (s.getUTF8Byte p h).IsUTF8FirstByte := by
  induction s using push_induction with
  | empty => simp [Pos.Raw.lt_iff]
  | push s c ih =>
    rw [isValid_push, ih]
    refine ⟨?_, ?_⟩
    · rintro ((rfl|⟨h, hb⟩)|h)
      · refine Or.inr ⟨by simp [Pos.Raw.lt_iff, Char.utf8Size_pos], ?_⟩
        simp only [getUTF8Byte, bytes_push, byteIdx_rawEndPos]
        rw [ByteArray.getElem_append_right (by simp)]
        simp [List.isUTF8FirstByte_getElem_utf8Encode_singleton]
      · refine Or.inr ⟨by simp [lt_iff] at h ⊢; omega, ?_⟩
        simp only [getUTF8Byte, bytes_push]
        rwa [ByteArray.getElem_append_left, ← getUTF8Byte]
      · exact Or.inl (by simpa [rawEndPos_push])
    · rintro (h|⟨h, hb⟩)
      · exact Or.inr (by simpa [rawEndPos_push] using h)
      · simp only [getUTF8Byte, bytes_push] at hb
        by_cases h' : p < s.rawEndPos
        · refine Or.inl (Or.inr ⟨h', ?_⟩)
          rwa [ByteArray.getElem_append_left h', ← getUTF8Byte] at hb
        · refine Or.inl (Or.inl ?_)
          rw [ByteArray.getElem_append_right (by simp [lt_iff] at h' ⊢; omega)] at hb
          simp only [size_bytes, List.isUTF8FirstByte_getElem_utf8Encode_singleton] at hb
          ext
          simp only [lt_iff, byteIdx_rawEndPos, Nat.not_lt] at ⊢ h'
          omega

/--
Returns `true` if `p` is a valid UTF-8 position in the string `s`.

This means that `p ≤ s.rawEndPos` and `p` lies on a UTF-8 character boundary. At runtime, this
operation takes constant time.

Examples:
 * `String.Pos.isValid "abc" ⟨0⟩ = true`
 * `String.Pos.isValid "abc" ⟨1⟩ = true`
 * `String.Pos.isValid "abc" ⟨3⟩ = true`
 * `String.Pos.isValid "abc" ⟨4⟩ = false`
 * `String.Pos.isValid "𝒫(A)" ⟨0⟩ = true`
 * `String.Pos.isValid "𝒫(A)" ⟨1⟩ = false`
 * `String.Pos.isValid "𝒫(A)" ⟨2⟩ = false`
 * `String.Pos.isValid "𝒫(A)" ⟨3⟩ = false`
 * `String.Pos.isValid "𝒫(A)" ⟨4⟩ = true`
-/
@[extern "lean_string_is_valid_pos", expose]
def Pos.Raw.isValid (s : @&String) (p : @& Pos.Raw) : Bool :=
  if h : p < s.rawEndPos then
    (s.getUTF8Byte p h).IsUTF8FirstByte
  else
    p = s.rawEndPos

@[simp]
theorem Pos.Raw.isValid_eq_true_iff {s : String} {p : Pos.Raw} : p.isValid s = true ↔ p.IsValid s := by
  rw [isValid_iff_isUTF8FirstByte]
  fun_cases isValid s p with
  | case1 h =>
    simp_all only [decide_eq_true_eq, exists_true_left, iff_or_self]
    rintro rfl
    simp [lt_iff] at h
  | case2 => simp_all

@[simp]
theorem Pos.Raw.isValid_eq_false_iff {s : String} {p : Pos.Raw} : p.isValid s = false ↔ ¬ p.IsValid s := by
  rw [← Bool.not_eq_true, Pos.Raw.isValid_eq_true_iff]

instance {s : String} {p : Pos.Raw} : Decidable (p.IsValid s) :=
  decidable_of_iff (p.isValid s = true) Pos.Raw.isValid_eq_true_iff

theorem Pos.Raw.isValid_iff_isSome_utf8DecodeChar? {s : String} {p : Pos.Raw} :
    p.IsValid s ↔ p = s.rawEndPos ∨ (s.bytes.utf8DecodeChar? p.byteIdx).isSome := by
  refine ⟨?_, fun h => h.elim (by rintro rfl; simp) (fun h => ?_)⟩
  · induction s using push_induction with
    | empty => simp [ByteArray.utf8DecodeChar?]
    | push s c ih =>
      simp only [isValid_push, bytes_push]
      refine ?_ ∘ Or.imp_left ih
      rintro ((rfl|h)|rfl)
      · rw [ByteArray.utf8DecodeChar?_eq_utf8DecodeChar?_extract, ByteArray.extract_append_eq_right (by simp) (by simp)]
        simp
      · exact Or.inr (ByteArray.isSome_utf8DecodeChar?_append h _)
      · simp [rawEndPos_push]
  · refine isValid_iff_isUTF8FirstByte.2 (Or.inr ?_)
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 h
    refine ⟨?_, ?_⟩
    · have := ByteArray.le_size_of_utf8DecodeChar?_eq_some hc
      have := c.utf8Size_pos
      simp only [lt_iff, byteIdx_rawEndPos, gt_iff_lt, ← size_bytes]
      omega
    · rw [getUTF8Byte]
      exact ByteArray.isUTF8FirstByte_of_isSome_utf8DecodeChar? h

theorem _root_.ByteArray.IsValidUTF8.isUTF8FirstByte_getElem_zero {b : ByteArray}
    (h : b.IsValidUTF8) (h₀ : 0 < b.size) : b[0].IsUTF8FirstByte := by
  rcases h with ⟨m, rfl⟩
  have : m ≠ [] := by
    rintro rfl
    simp at h₀
  conv => congr; congr; rw [← List.cons_head_tail this, ← List.singleton_append, List.utf8Encode_append]
  rw [ByteArray.getElem_append_left]
  · exact List.isUTF8FirstByte_getElem_utf8Encode_singleton.2 rfl
  · simp [List.utf8Encode_singleton, Char.utf8Size_pos]

theorem isUTF8FirstByte_getUTF8Byte_zero {b : String} {h} : (b.getUTF8Byte 0 h).IsUTF8FirstByte :=
  b.isValidUTF8.isUTF8FirstByte_getElem_zero _

theorem Pos.Raw.isValidUTF8_extract_iff {s : String} (p₁ p₂ : Pos.Raw) (hle : p₁ ≤ p₂) (hle' : p₂ ≤ s.rawEndPos) :
    (s.bytes.extract p₁.byteIdx p₂.byteIdx).IsValidUTF8 ↔ p₁ = p₂ ∨ (p₁.IsValid s ∧ p₂.IsValid s) := by
  have hle'' : p₂.byteIdx ≤ s.bytes.size := by simpa [le_iff] using hle'
  refine ⟨fun h => Classical.or_iff_not_imp_left.2 (fun h' => ?_), ?_⟩
  · have hlt : p₁ < p₂ := by
      simp_all [le_iff, lt_iff, Pos.Raw.ext_iff]
      omega
    have h₁ : p₁.IsValid s := by
      rw [isValid_iff_isUTF8FirstByte]
      refine Or.inr ⟨Pos.Raw.lt_of_lt_of_le hlt hle', ?_⟩
      have hlt' : 0 < p₂.byteIdx - p₁.byteIdx := by
        simp [lt_iff] at hlt
        omega
      have := h.isUTF8FirstByte_getElem_zero
      simp only [ByteArray.size_extract, Nat.min_eq_left hle'', hlt', ByteArray.getElem_extract, Nat.add_zero] at this
      simp [getUTF8Byte, this trivial]
    refine ⟨h₁, isValid_iff_isValidUTF8_extract_zero.2 ⟨hle', ?_⟩⟩
    rw [ByteArray.extract_eq_extract_append_extract p₁.byteIdx (by simp) hle]
    exact h₁.isValidUTF8_extract_zero.append h
  · refine fun h => h.elim (by rintro rfl; simp) (fun ⟨h₁, h₂⟩ => ?_)
    let t : String := ⟨_, h₂.isValidUTF8_extract_zero⟩
    have htb : t.bytes = s.bytes.extract 0 p₂.byteIdx := rfl
    have ht : p₁.IsValid t := by
      refine isValid_iff_isValidUTF8_extract_zero.2 ⟨?_, ?_⟩
      · simpa [le_iff, t, Nat.min_eq_left hle'', ← size_bytes]
      · simpa [htb, ByteArray.extract_extract, Nat.min_eq_left (le_iff.1 hle)] using h₁.isValidUTF8_extract_zero
    simpa [htb, ByteArray.extract_extract, Nat.zero_add, Nat.min_eq_left hle'', ← size_bytes]
      using ht.isValidUTF8_extract_utf8ByteSize

theorem Pos.Raw.isValid_iff_isValidUTF8_extract_utf8ByteSize {s : String} {p : Pos.Raw} :
    p.IsValid s ↔ p ≤ s.rawEndPos ∧ (s.bytes.extract p.byteIdx s.utf8ByteSize).IsValidUTF8 := by
  refine ⟨fun h => ⟨h.le_rawEndPos, h.isValidUTF8_extract_utf8ByteSize⟩, fun ⟨h₁, h₂⟩ => ?_⟩
  rw [← byteIdx_rawEndPos, isValidUTF8_extract_iff _ _ h₁ (by simp)] at h₂
  obtain (rfl|h₂) := h₂
  · simp
  · exact h₂.1

theorem ValidPos.isValidUTF8_extract {s : String} (pos₁ pos₂ : s.ValidPos) :
    (s.bytes.extract pos₁.offset.byteIdx pos₂.offset.byteIdx).IsValidUTF8 := by
  by_cases h : pos₁ ≤ pos₂
  · exact (Pos.Raw.isValidUTF8_extract_iff _ _   h pos₂.isValid.le_rawEndPos).2 (Or.inr ⟨pos₁.isValid, pos₂.isValid⟩)
  · rw [ByteArray.extract_eq_empty_iff.2]
    · exact ByteArray.isValidUTF8_empty
    · rw [Nat.min_eq_left]
      · rw [ValidPos.le_iff, Pos.Raw.le_iff] at h
        omega
      · have := Pos.Raw.le_iff.1 pos₂.isValid.le_rawEndPos
        rwa [size_bytes, ← byteIdx_rawEndPos]

@[extern "lean_string_utf8_extract"]
def ValidPos.extract {s : @& String} (b e : @& s.ValidPos) : String where
  bytes := s.bytes.extract b.offset.byteIdx e.offset.byteIdx
  isValidUTF8 := b.isValidUTF8_extract e

/-- Creates a `String` from a `String.Slice` by copying the bytes. -/
@[inline]
def Slice.copy (s : Slice) : String :=
  s.startInclusive.extract s.endExclusive

theorem Slice.bytes_copy {s : Slice} :
    s.copy.bytes = s.str.bytes.extract s.startInclusive.offset.byteIdx s.endExclusive.offset.byteIdx := (rfl)

@[simp]
theorem Slice.utf8ByteSize_copy {s : Slice} :
    s.copy.utf8ByteSize = s.endExclusive.offset.byteIdx - s.startInclusive.offset.byteIdx:= by
  simp [← size_bytes, bytes_copy]
  rw [Nat.min_eq_left (by simpa [Pos.Raw.le_iff] using s.endExclusive.isValid.le_rawEndPos)]

@[simp]
theorem Slice.rawEndPos_copy {s : Slice} : s.copy.rawEndPos = s.rawEndPos := by
  simp [Pos.Raw.ext_iff, utf8ByteSize_eq]

theorem Slice.getUTF8Byte_eq_getUTF8Byte_copy {s : Slice} {p : Pos.Raw} {h : p < s.rawEndPos} :
    s.getUTF8Byte p h = s.copy.getUTF8Byte p (by simpa) := by
  simp [getUTF8Byte, String.getUTF8Byte, bytes_copy, ByteArray.getElem_extract]

theorem Slice.getUTF8Byte_copy {s : Slice} {p : Pos.Raw} {h} :
    s.copy.getUTF8Byte p h = s.getUTF8Byte p (by simpa using h) := by
  rw [getUTF8Byte_eq_getUTF8Byte_copy]

theorem Slice.isUTF8FirstByte_utf8ByteAt_zero {s : Slice} {h} :
    (s.getUTF8Byte 0 h).IsUTF8FirstByte := by
  simpa [getUTF8Byte_eq_getUTF8Byte_copy] using s.copy.isUTF8FirstByte_getUTF8Byte_zero

@[simp]
theorem Pos.Raw.isValid_copy_iff {s : Slice} {p : Pos.Raw} :
    p.IsValid s.copy ↔ p.IsValidForSlice s := by
  rw [isValid_iff_isValidUTF8_extract_zero]
  refine ⟨fun ⟨h₁, h₂⟩ => ⟨?_, ?_⟩, fun ⟨h₁, h₂⟩ => ⟨?_, ?_⟩⟩
  · simpa using h₁
  · have := s.startInclusive_le_endExclusive
    simp_all only [Slice.rawEndPos_copy, le_iff, Slice.byteIdx_rawEndPos, Slice.utf8ByteSize_eq,
      ValidPos.le_iff]
    rw [Slice.bytes_copy, ByteArray.extract_extract, Nat.add_zero, Nat.min_eq_left (by omega)] at h₂
    rw [← byteIdx_offsetBy, Pos.Raw.isValidUTF8_extract_iff] at h₂
    · rcases h₂ with (h₂|⟨-, h₂⟩)
      · rw [← h₂]
        exact s.startInclusive.isValid
      · exact h₂
    · simp [le_iff]
    · have := s.endExclusive.isValid.le_rawEndPos
      simp_all [le_iff]
      omega
  · simpa using h₁
  · have := s.startInclusive_le_endExclusive
    simp_all only [le_iff, Slice.byteIdx_rawEndPos, Slice.utf8ByteSize_eq, ValidPos.le_iff]
    rw [Slice.bytes_copy, ByteArray.extract_extract, Nat.add_zero, Nat.min_eq_left (by omega)]
    rw [← byteIdx_offsetBy, Pos.Raw.isValidUTF8_extract_iff]
    · exact Or.inr ⟨s.startInclusive.isValid, h₂⟩
    · simp [le_iff]
    · have := s.endExclusive.isValid.le_rawEndPos
      simp_all [le_iff]
      omega

theorem Pos.Raw.isValidForSlice_iff_isUTF8FirstByte {s : Slice} {p : Pos.Raw} :
    p.IsValidForSlice s ↔ (p = s.rawEndPos ∨ (∃ (h : p < s.rawEndPos), (s.getUTF8Byte p h).IsUTF8FirstByte)) := by
  simp [← isValid_copy_iff, isValid_iff_isUTF8FirstByte, Slice.getUTF8Byte_copy]

/-- Efficiently checks whether a position is at a UTF-8 character boundary of the slice `s`. -/
@[expose]
def Pos.Raw.isValidForSlice (s : Slice) (p : Pos.Raw) : Bool :=
  if h : p < s.rawEndPos then
    (s.getUTF8Byte p h).IsUTF8FirstByte
  else
    p = s.rawEndPos

@[simp]
theorem Pos.Raw.isValidForSlice_eq_true_iff {s : Slice} {p : Pos.Raw} :
    p.isValidForSlice s = true ↔ p.IsValidForSlice s := by
  rw [isValidForSlice_iff_isUTF8FirstByte]
  fun_cases isValidForSlice with
  | case1 h =>
    simp_all only [decide_eq_true_eq, exists_true_left, iff_or_self]
    rintro rfl
    simp [lt_iff] at h
  | case2 => simp_all

@[simp]
theorem Pos.Raw.isValidForSlice_eq_false_iff {s : Slice} {p : Pos.Raw} :
    p.isValidForSlice s = false ↔ ¬ p.IsValidForSlice s := by
  rw [← Bool.not_eq_true, isValidForSlice_eq_true_iff]

instance {s : Slice} {p : Pos.Raw} : Decidable (p.IsValidForSlice s) :=
  decidable_of_iff _ Pos.Raw.isValidForSlice_eq_true_iff

theorem Pos.Raw.isValidForSlice_iff_isSome_utf8DecodeChar?_copy {s : Slice} {p : Pos.Raw} :
    p.IsValidForSlice s ↔ p = s.rawEndPos ∨ (s.copy.bytes.utf8DecodeChar? p.byteIdx).isSome := by
  rw [← isValid_copy_iff, isValid_iff_isSome_utf8DecodeChar?, Slice.rawEndPos_copy]

theorem Slice.bytes_str_eq {s : Slice} :
    s.str.bytes = s.str.bytes.extract 0 s.startInclusive.offset.byteIdx ++
      s.copy.bytes ++ s.str.bytes.extract s.endExclusive.offset.byteIdx s.str.bytes.size := by
  rw [bytes_copy, ← ByteArray.extract_eq_extract_append_extract, ← ByteArray.extract_eq_extract_append_extract,
    ByteArray.extract_zero_size]
  · simp
  · simpa [Pos.Raw.le_iff] using s.endExclusive.isValid.le_rawEndPos
  · simp
  · simpa [Pos.Raw.le_iff] using s.startInclusive_le_endExclusive

theorem Pos.Raw.isValidForSlice_iff_isSome_utf8DecodeChar? {s : Slice} {p : Pos.Raw} :
    p.IsValidForSlice s ↔ p = s.rawEndPos ∨ (p < s.rawEndPos ∧ (s.str.bytes.utf8DecodeChar? (s.startInclusive.offset.byteIdx + p.byteIdx)).isSome) := by
  refine ⟨?_, ?_⟩
  · rw [isValidForSlice_iff_isSome_utf8DecodeChar?_copy]
    rintro (rfl|h)
    · simp
    · refine Or.inr ⟨?_, ?_⟩
      · have := ByteArray.lt_size_of_isSome_utf8DecodeChar? h
        simpa [Pos.Raw.lt_iff] using this
      · rw [ByteArray.utf8DecodeChar?_eq_utf8DecodeChar?_extract] at h
        rw [Slice.bytes_str_eq, ByteArray.append_assoc, ByteArray.utf8DecodeChar?_eq_utf8DecodeChar?_extract]
        simp only [ByteArray.size_append, ByteArray.size_extract, Nat.sub_zero, Nat.le_refl,
          Nat.min_eq_left]
        have h' : s.startInclusive.offset.byteIdx ≤ s.str.bytes.size := by
          simpa [le_iff] using s.startInclusive.isValid.le_rawEndPos
        rw [Nat.min_eq_left h', ByteArray.extract_append_size_add' (by simp [size_bytes ▸ h']),
          ByteArray.extract_append, Nat.add_sub_cancel_left]
        rw [ByteArray.extract_eq_extract_append_extract s.copy.bytes.size]
        · rw [ByteArray.append_assoc]
          apply ByteArray.isSome_utf8DecodeChar?_append h
        · have := ByteArray.lt_size_of_isSome_utf8DecodeChar? h
          simp only [size_bytes, Slice.utf8ByteSize_copy, ByteArray.size_extract, Nat.le_refl,
            Nat.min_eq_left] at this
          simp only [size_bytes, Slice.utf8ByteSize_copy, ge_iff_le]
          omega
        · simp
  · rw [isValidForSlice_iff_isUTF8FirstByte]
    rintro (rfl|⟨h₁, h₂⟩)
    · simp
    · exact Or.inr ⟨h₁, ByteArray.isUTF8FirstByte_of_isSome_utf8DecodeChar? h₂⟩

theorem Slice.Pos.isUTF8FirstByte_byte {s : Slice} {pos : s.Pos} {h : pos ≠ s.endPos} :
    (pos.byte h).IsUTF8FirstByte :=
  ((Pos.Raw.isValidForSlice_iff_isUTF8FirstByte.1 pos.isValidForSlice).elim (fun h' => (h (Pos.ext h')).elim) (·.2))

/-- Given a valid position on a slice `s`, obtains the corresponding valid position on the
underlying string `s.str`. -/
@[inline]
def Slice.Pos.str {s : Slice} (pos : s.Pos) : s.str.ValidPos where
  offset := pos.offset.offsetBy s.startInclusive.offset
  isValid := pos.isValidForSlice.isValid_offsetBy

@[simp]
theorem Slice.Pos.offset_str {s : Slice} {pos : s.Pos} :
    pos.str.offset = pos.offset.offsetBy s.startInclusive.offset := (rfl)

@[simp]
theorem Slice.Pos.offset_str_le_offset_endExclusive {s : Slice} {pos : s.Pos} :
    pos.str.offset ≤ s.endExclusive.offset := by
  have := pos.isValidForSlice.le_rawEndPos
  have := s.startInclusive_le_endExclusive
  simp only [Pos.Raw.le_iff, byteIdx_rawEndPos, utf8ByteSize_eq, offset_str,
    Pos.Raw.byteIdx_offsetBy, ValidPos.le_iff] at *
  omega

theorem Slice.Pos.offset_le_offset_str {s : Slice} {pos : s.Pos} :
    pos.offset ≤ pos.str.offset := by
  simp [String.Pos.Raw.le_iff]

@[simp]
theorem Slice.Pos.offset_le_offset_endExclusive {s : Slice} {pos : s.Pos} :
    pos.offset ≤ s.endExclusive.offset :=
  Pos.Raw.le_trans offset_le_offset_str offset_str_le_offset_endExclusive

/-- Given a slice and a valid position within the slice, obtain a new slice on the same underlying
string by replacing the start of the slice with the given position. -/
@[inline, expose] -- for the defeq `(s.replaceStart pos).str = s.str`
def Slice.replaceStart (s : Slice) (pos : s.Pos) : Slice where
  str := s.str
  startInclusive := pos.str
  endExclusive := s.endExclusive
  startInclusive_le_endExclusive := Pos.offset_str_le_offset_endExclusive

@[simp]
theorem Slice.str_replaceStart {s : Slice} {pos : s.Pos} :
    (s.replaceStart pos).str = s.str := rfl

@[simp]
theorem Slice.startInclusive_replaceStart {s : Slice} {pos : s.Pos} :
    (s.replaceStart pos).startInclusive = pos.str := rfl

@[simp]
theorem Slice.endExclusive_replaceStart {s : Slice} {pos : s.Pos} :
    (s.replaceStart pos).endExclusive = s.endExclusive := rfl

/-- Given a slice and a valid position within the slice, obtain a new slice on the same underlying
string by replacing the end of the slice with the given position. -/
@[inline, expose] -- for the defeq `(s.replaceEnd pos).str = s.str`
def Slice.replaceEnd (s : Slice) (pos : s.Pos) : Slice where
  str := s.str
  startInclusive := s.startInclusive
  endExclusive := pos.str
  startInclusive_le_endExclusive := by simp [ValidPos.le_iff, String.Pos.Raw.le_iff]

@[simp]
theorem Slice.str_replaceEnd {s : Slice} {pos : s.Pos} :
    (s.replaceEnd pos).str = s.str := rfl

@[simp]
theorem Slice.startInclusive_replaceEnd {s : Slice} {pos : s.Pos} :
    (s.replaceEnd pos).startInclusive = s.startInclusive := rfl

@[simp]
theorem Slice.endExclusive_replaceEnd {s : Slice} {pos : s.Pos} :
    (s.replaceEnd pos).endExclusive = pos.str := rfl

/-- Given a slice and two valid positions within the slice, obtain a new slice on the same underlying
string formed by the new bounds. -/
@[inline, expose] -- for the defeq `(s.replaceStartEnd newStart newEnd).str = s.str`
def Slice.replaceStartEnd (s : Slice) (newStart newEnd : s.Pos)
    (h : newStart.offset ≤ newEnd.offset) : Slice where
  str := s.str
  startInclusive := newStart.str
  endExclusive := newEnd.str
  startInclusive_le_endExclusive := by simpa [ValidPos.le_iff, Pos.Raw.le_iff] using h

@[simp]
theorem Slice.str_replaceStartEnd {s : Slice} {newStart newEnd : s.Pos} {h} :
    (s.replaceStartEnd newStart newEnd h).str = s.str := rfl

@[simp]
theorem Slice.startInclusive_replaceStartEnd {s : Slice} {newStart newEnd : s.Pos} {h} :
    (s.replaceStartEnd newStart newEnd h).startInclusive = newStart.str := rfl

@[simp]
theorem Slice.endExclusive_replaceStartEnd {s : Slice} {newStart newEnd : s.Pos} {h} :
    (s.replaceStartEnd newStart newEnd h).endExclusive = newEnd.str := rfl

/-- Given a slice and two valid positions within the slice, obtain a new slice on the same underlying
string formed by the new bounds, or panic if the given end is strictly less than the given start. -/
def Slice.replaceStartEnd! (s : Slice) (newStart newEnd : s.Pos) : Slice :=
  if h : newStart.offset ≤ newEnd.offset then
    s.replaceStartEnd newStart newEnd h
  else
    panic! "Starting position must be less than or equal to end position."

@[simp]
theorem Slice.utf8ByteSize_replaceStart {s : Slice} {pos : s.Pos} :
    (s.replaceStart pos).utf8ByteSize = s.utf8ByteSize - pos.offset.byteIdx := by
  simp only [utf8ByteSize_eq, str_replaceStart, endExclusive_replaceStart,
    startInclusive_replaceStart, Pos.offset_str, Pos.Raw.byteIdx_offsetBy]
  omega

theorem Slice.rawEndPos_replaceStart {s : Slice} {pos : s.Pos} :
    (s.replaceStart pos).rawEndPos = s.rawEndPos.unoffsetBy pos.offset := by
  ext
  simp

@[simp]
theorem Slice.utf8ByteSize_replaceEnd {s : Slice} {pos : s.Pos} :
    (s.replaceEnd pos).utf8ByteSize = pos.offset.byteIdx := by
  simp [utf8ByteSize_eq]

@[simp]
theorem Slice.rawEndPos_replaceEnd {s : Slice} {pos : s.Pos} :
    (s.replaceEnd pos).rawEndPos = pos.offset := by
  ext
  simp

@[simp]
theorem Slice.utf8ByteSize_replaceStartEnd {s : Slice} {newStart newEnd : s.Pos} {h} :
    (s.replaceStartEnd newStart newEnd h).utf8ByteSize = newStart.offset.byteDistance newEnd.offset := by
  simp [utf8ByteSize_eq, Pos.Raw.byteDistance_eq]
  omega

theorem Pos.Raw.isValidForSlice_replaceStart {s : Slice} {p : s.Pos} {off : Pos.Raw} :
    off.IsValidForSlice (s.replaceStart p) ↔ (off.offsetBy p.offset).IsValidForSlice s := by
  refine ⟨fun ⟨h₁, h₂⟩ => ⟨?_, ?_⟩, fun ⟨h₁, h₂⟩ => ⟨?_, ?_⟩⟩
  · have := p.isValidForSlice.le_rawEndPos
    simp_all [le_iff]
    omega
  · simpa [Pos.Raw.offsetBy_assoc] using h₂
  · simp_all [Pos.Raw.le_iff]
    omega
  · simpa [Pos.Raw.offsetBy_assoc] using h₂

theorem Pos.Raw.isValidForSlice_replaceEnd {s : Slice} {p : s.Pos} {off : Pos.Raw} :
    off.IsValidForSlice (s.replaceEnd p) ↔ off ≤ p.offset ∧ off.IsValidForSlice s := by
  refine ⟨fun ⟨h₁, h₂⟩ => ⟨?_, ?_, ?_⟩, fun ⟨h₁, ⟨h₂, h₃⟩⟩ => ⟨?_, ?_⟩⟩
  · simpa using h₁
  · simp only [Slice.rawEndPos_replaceEnd] at h₁
    exact Pos.Raw.le_trans h₁ p.isValidForSlice.le_rawEndPos
  · simpa using h₂
  · simpa using h₁
  · simpa using h₃

@[extern "lean_string_utf8_get", expose]
def decodeChar (s : @& String) (byteIdx : @& Nat) (h : (s.bytes.utf8DecodeChar? byteIdx).isSome) : Char :=
  s.bytes.utf8DecodeChar byteIdx h

/-- Obtains the character at the given position in the string. -/
@[inline, expose]
def Slice.Pos.get {s : Slice} (pos : s.Pos) (h : pos ≠ s.endPos) : Char :=
  s.str.decodeChar (s.startInclusive.offset.byteIdx + pos.offset.byteIdx)
    ((Pos.Raw.isValidForSlice_iff_isSome_utf8DecodeChar?.1 pos.isValidForSlice).elim (by simp_all [Pos.ext_iff]) (·.2))

theorem Slice.Pos.get_eq_utf8DecodeChar {s : Slice} (pos : s.Pos) (h : pos ≠ s.endPos) :
    pos.get h = s.str.bytes.utf8DecodeChar (s.startInclusive.offset.byteIdx + pos.offset.byteIdx)
      ((Pos.Raw.isValidForSlice_iff_isSome_utf8DecodeChar?.1 pos.isValidForSlice).elim (by simp_all [Pos.ext_iff]) (·.2)) := (rfl)

/-- Returns the byte at the given position in the string, or `none` if the position is the end
position. -/
@[expose]
def Slice.Pos.get? {s : Slice} (pos : s.Pos) : Option Char :=
  if h : pos = s.endPos then none else some (pos.get h)

/-- Returns the byte at the given position in the string, or panicks if the position is the end
position. -/
@[expose]
def Slice.Pos.get! {s : Slice} (pos : s.Pos) : Char :=
  if h : pos = s.endPos then panic! "Cannot retrieve character at end position" else pos.get h

@[simp]
theorem startInclusive_toSlice {s : String} : s.toSlice.startInclusive = s.startValidPos := rfl

@[simp]
theorem endExclusive_toSlice {s : String} : s.toSlice.endExclusive = s.endValidPos := rfl

@[simp]
theorem str_toSlice {s : String} : s.toSlice.str = s := rfl

@[simp]
theorem copy_toSlice {s : String} : s.toSlice.copy = s := by
  simp [← bytes_inj, Slice.bytes_copy, ← size_bytes]

@[simp]
theorem Pos.Raw.isValidForSlice_toSlice_iff {s : String} {p : Pos.Raw} :
    p.IsValidForSlice s.toSlice ↔ p.IsValid s := by
  rw [← isValid_copy_iff, copy_toSlice]

theorem Pos.Raw.IsValid.toSlice {s : String} {p : Pos.Raw} (h : p.IsValid s) :
    p.IsValidForSlice s.toSlice :=
  isValidForSlice_toSlice_iff.2 h

theorem Pos.Raw.IsValidForSlice.ofSlice {s : String} {p : Pos.Raw} (h : p.IsValidForSlice s.toSlice) :
    p.IsValid s :=
  isValidForSlice_toSlice_iff.1 h

/-- Turns a valid position on the string `s` into a valid position on the slice `s.toSlice`. -/
@[inline, expose]
def ValidPos.toSlice {s : String} (pos : s.ValidPos) : s.toSlice.Pos where
  offset := pos.offset
  isValidForSlice := pos.isValid.toSlice

@[simp]
theorem ValidPos.offset_toSlice {s : String} {pos : s.ValidPos} : pos.toSlice.offset = pos.offset := (rfl)

/-- Given a string `s`, turns a valid position on the slice `s.toSlice` into a valid position on the
string `s`. -/
@[inline, expose]
def Slice.Pos.ofSlice {s : String} (pos : s.toSlice.Pos) : s.ValidPos where
  offset := pos.offset
  isValid := pos.isValidForSlice.ofSlice

@[simp]
theorem Slice.Pos.offset_ofSlice {s : String} {pos : s.toSlice.Pos} : pos.ofSlice.offset = pos.offset := (rfl)

@[simp]
theorem rawEndPos_toSlice {s : String} : s.toSlice.rawEndPos = s.rawEndPos := by
  rw [← Slice.rawEndPos_copy, copy_toSlice]

@[simp]
theorem endPos_toSlice {s : String} : s.toSlice.endPos = s.endValidPos.toSlice :=
  Slice.Pos.ext (by simp)

@[simp]
theorem startPos_toSlice {s : String} : s.toSlice.startPos = s.startValidPos.toSlice :=
  Slice.Pos.ext (by simp)

@[simp]
theorem ValidPos.ofSlice_toSlice {s : String} (pos : s.ValidPos) : pos.toSlice.ofSlice = pos :=
  ValidPos.ext (by simp)

@[simp]
theorem Slice.Pos.toSlice_ofSlice {s : String} (pos : s.toSlice.Pos) : pos.ofSlice.toSlice = pos :=
  Slice.Pos.ext (by simp)

@[simp]
theorem Slice.Pos.toSlice_comp_ofSlice {s : String} :
    ValidPos.toSlice ∘ (ofSlice (s := s)) = id := by ext; simp

@[simp]
theorem ValidPos.ofSlice_comp_toSlice {s : String} :
    Slice.Pos.ofSlice ∘ (toSlice (s := s)) = id := by ext; simp

theorem ValidPos.toSlice_inj {s : String} {p q : s.ValidPos} : p.toSlice = q.toSlice ↔ p = q :=
  ⟨fun h => by simpa using congrArg Slice.Pos.ofSlice h, (· ▸ rfl)⟩

theorem Slice.Pos.ofSlice_inj {s : String} {p q : s.toSlice.Pos} : p.ofSlice = q.ofSlice ↔ p = q :=
  ⟨fun h => by simpa using congrArg ValidPos.toSlice h, (· ▸ rfl)⟩

@[simp]
theorem ValidPos.toSlice_le {s : String} {p q : s.ValidPos} : p.toSlice ≤ q.toSlice ↔ p ≤ q := by
  simp [le_iff, Slice.Pos.le_iff]

@[simp]
theorem Slice.Pos.ofSlice_le {s : String} {p q : s.toSlice.Pos} :
    p.ofSlice ≤ q.ofSlice ↔ p ≤ q := by
  simp [ValidPos.le_iff, le_iff]

@[simp]
theorem ValidPos.toSlice_lt {s : String} {p q : s.ValidPos} : p.toSlice < q.toSlice ↔ p < q := by
  simp [lt_iff, Slice.Pos.lt_iff]

@[simp]
theorem Slice.Pos.ofSlice_lt {s : String} {p q : s.toSlice.Pos} :
    p.ofSlice < q.ofSlice ↔ p < q := by
  simp [ValidPos.lt_iff, lt_iff]

/--
Returns the character at the position `pos` of a string, taking a proof that `p` is not the
past-the-end position.

This function is overridden with an efficient implementation in runtime code.

Examples:
* `("abc".pos ⟨1⟩ (by decide)).get (by decide) = 'b'`
* `("L∃∀N".pos ⟨1⟩ (by decide)).get (by decide) = '∃'`
-/
@[inline, expose]
def ValidPos.get {s : String} (pos : s.ValidPos) (h : pos ≠ s.endValidPos) : Char :=
  pos.toSlice.get (ne_of_apply_ne Slice.Pos.ofSlice (by simp [h]))

/--
Returns the character at the position `pos` of a string, or `none` if the position is the
past-the-end position.

This function is overridden with an efficient implementation in runtime code.
-/
@[inline, expose]
def ValidPos.get? {s : String} (pos : s.ValidPos) : Option Char :=
  pos.toSlice.get?

/--
Returns the character at the position `pos` of a string, or panics if the position is the
past-the-end position.

This function is overridden with an efficient implementation in runtime code.
-/
@[inline, expose]
def ValidPos.get! {s : String} (pos : s.ValidPos) : Char :=
  pos.toSlice.get!

/--
Returns the byte at the position `pos` of a string.
-/
@[inline, expose]
def ValidPos.byte {s : String} (pos : s.ValidPos) (h : pos ≠ s.endValidPos) : UInt8 :=
  pos.toSlice.byte (ne_of_apply_ne Slice.Pos.ofSlice (by simp [h]))

theorem ValidPos.isUTF8FirstByte_byte {s : String} {pos : s.ValidPos} {h : pos ≠ s.endValidPos} :
    (pos.byte h).IsUTF8FirstByte :=
  Slice.Pos.isUTF8FirstByte_byte

@[simp]
theorem startValidPos_eq_endValidPos_iff {b : String} : b.startValidPos = b.endValidPos ↔ b = "" := by
  simp [← utf8ByteSize_eq_zero_iff, ValidPos.ext_iff, Eq.comm (b := b.rawEndPos)]

theorem isSome_utf8DecodeChar?_zero {b : String} (hb : b ≠ "") : (b.bytes.utf8DecodeChar? 0).isSome := by
  refine (((Pos.Raw.isValid_iff_isSome_utf8DecodeChar? (s := b)).1 Pos.Raw.isValid_zero).elim ?_ id)
  rw [eq_comm, rawEndPos_eq_zero_iff]
  exact fun h => (hb h).elim

theorem head_data {b : String} {h} :
    b.data.head h = b.bytes.utf8DecodeChar 0 (isSome_utf8DecodeChar?_zero (by simpa using h)) := by
  obtain ⟨l, rfl⟩ := b.exists_eq_asString
  match l with
  | [] => simp at h
  | c::cs => simp

theorem get_startValidPos {b : String} (h) :
    b.startValidPos.get h = b.data.head (by rwa [ne_eq, data_eq_nil_iff, ← startValidPos_eq_endValidPos_iff]) :=
  head_data.symm

theorem eq_singleton_append {s : String} (h : s.startValidPos ≠ s.endValidPos) :
    ∃ t, s = singleton (s.startValidPos.get h) ++ t := by
  obtain ⟨m, rfl⟩ := s.exists_eq_asString
  have hm : m ≠ [] := by
    rwa [ne_eq, ← List.asString_eq_empty_iff, ← startValidPos_eq_endValidPos_iff]
  refine ⟨m.tail.asString, ?_⟩
  rw (occs := [1]) [← List.cons_head_tail hm]
  rw [← List.singleton_append, List.asString_append, append_left_inj, ← singleton_eq_asString,
    get_startValidPos]
  simp

theorem Slice.copy_eq_copy_replaceEnd {s : Slice} {pos : s.Pos} :
    s.copy = (s.replaceEnd pos).copy ++ (s.replaceStart pos).copy := by
  rw [← String.bytes_inj, bytes_copy, bytes_append, bytes_copy, bytes_copy]
  simp only [str_replaceEnd, startInclusive_replaceEnd, endExclusive_replaceEnd, Pos.offset_str,
    Pos.Raw.byteIdx_offsetBy, str_replaceStart, startInclusive_replaceStart,
    endExclusive_replaceStart, ByteArray.extract_append_extract, Nat.le_add_right, Nat.min_eq_left]
  rw [Nat.max_eq_right]
  exact pos.offset_str_le_offset_endExclusive

/-- Given a slice `s` and a position on `s.copy`, obtain the corresponding position on `s`. -/
@[inline]
def ValidPos.ofCopy {s : Slice} (pos : s.copy.ValidPos) : s.Pos where
  offset := pos.offset
  isValidForSlice := Pos.Raw.isValid_copy_iff.1 pos.isValid

@[simp]
theorem ValidPos.offset_ofCopy {s : Slice} {pos : s.copy.ValidPos} : pos.ofCopy.offset = pos.offset := (rfl)

/-- Given a slice `s` and a position on `s`, obtain the corresponding position on `s.copy.` -/
@[inline]
def Slice.Pos.toCopy {s : Slice} (pos : s.Pos) : s.copy.ValidPos where
  offset := pos.offset
  isValid := Pos.Raw.isValid_copy_iff.2 pos.isValidForSlice

@[simp]
theorem Slice.Pos.offset_toCopy {s : Slice} {pos : s.Pos} : pos.toCopy.offset = pos.offset := (rfl)

@[simp]
theorem Slice.Pos.ofCopy_toCopy {s : Slice} {pos : s.Pos} : pos.toCopy.ofCopy = pos :=
  Slice.Pos.ext (by simp)

@[simp]
theorem ValidPos.toCopy_ofCopy {s : Slice} {pos : s.copy.ValidPos} : pos.ofCopy.toCopy = pos :=
  ValidPos.ext (by simp)

theorem ValidPos.ofCopy_inj {s : Slice} {pos pos' : s.copy.ValidPos} : pos.ofCopy = pos'.ofCopy ↔ pos = pos' :=
  ⟨fun h => by simpa using congrArg Slice.Pos.toCopy h, (· ▸ rfl)⟩

@[simp]
theorem Slice.startValidPos_copy {s : Slice} : s.copy.startValidPos = s.startPos.toCopy :=
  ValidPos.ext (by simp)

@[simp]
theorem Slice.endValidPos_copy {s : Slice} : s.copy.endValidPos = s.endPos.toCopy :=
  ValidPos.ext (by simp)

theorem Slice.Pos.get_toCopy {s : Slice} {pos : s.Pos} (h) :
    pos.toCopy.get h = pos.get (by rintro rfl; simp at h) := by
  rw [ValidPos.get, Slice.Pos.get_eq_utf8DecodeChar, Slice.Pos.get_eq_utf8DecodeChar]
  simp only [str_toSlice, bytes_copy, startInclusive_toSlice, startValidPos_copy, offset_toCopy,
    Slice.offset_startPos, Pos.Raw.byteIdx_zero, ValidPos.offset_toSlice, Nat.zero_add]
  rw [ByteArray.utf8DecodeChar_eq_utf8DecodeChar_extract]
  conv => lhs; congr; rw [ByteArray.extract_extract]
  conv => rhs; rw [ByteArray.utf8DecodeChar_eq_utf8DecodeChar_extract]
  exact ByteArray.utf8DecodeChar_extract_congr _ _ _

theorem Slice.Pos.get_eq_get_toCopy {s : Slice} {pos : s.Pos} {h} :
    pos.get h = pos.toCopy.get (ne_of_apply_ne ValidPos.ofCopy (by simp [h])) :=
  (get_toCopy _).symm

theorem Slice.Pos.byte_toCopy {s : Slice} {pos : s.Pos} (h) :
    pos.toCopy.byte h = pos.byte (by rintro rfl; simp at h) := by
  rw [ValidPos.byte, Slice.Pos.byte, Slice.Pos.byte]
  simp [getUTF8Byte, String.getUTF8Byte, bytes_copy, ByteArray.getElem_extract]

theorem Slice.Pos.byte_eq_byte_toCopy {s : Slice} {pos : s.Pos} {h} :
    pos.byte h = pos.toCopy.byte (ne_of_apply_ne ValidPos.ofCopy (by simp [h])) :=
  (byte_toCopy _).symm

/-- Given a position in `s.replaceStart p₀`, obtain the corresponding position in `s`. -/
@[inline]
def Slice.Pos.ofReplaceStart {s : Slice} {p₀ : s.Pos} (pos : (s.replaceStart p₀).Pos) : s.Pos where
  offset := pos.offset.offsetBy p₀.offset
  isValidForSlice := Pos.Raw.isValidForSlice_replaceStart.1 pos.isValidForSlice

@[simp]
theorem Slice.Pos.offset_ofReplaceStart {s : Slice} {p₀ : s.Pos} {pos : (s.replaceStart p₀).Pos} :
    (ofReplaceStart pos).offset = pos.offset.offsetBy p₀.offset := (rfl)

/-- Given a position in `s` that is at least `p₀`, obtain the corresponding position in
`s.replaceStart p₀`. -/
@[inline]
def Slice.Pos.toReplaceStart {s : Slice} (p₀ : s.Pos) (pos : s.Pos) (h : p₀ ≤ pos) :
    (s.replaceStart p₀).Pos where
  offset := pos.offset.unoffsetBy p₀.offset
  isValidForSlice := Pos.Raw.isValidForSlice_replaceStart.2 (by
    simpa [Pos.Raw.offsetBy_unoffsetBy_of_le (Pos.Raw.le_iff.1 h)] using pos.isValidForSlice)

@[simp]
theorem Slice.Pos.offset_toReplaceStart {s : Slice} {p₀ : s.Pos} {pos : s.Pos} {h} :
    (toReplaceStart p₀ pos h).offset = pos.offset.unoffsetBy p₀.offset := (rfl)

@[simp]
theorem Slice.Pos.ofReplaceStart_startPos {s : Slice} {pos : s.Pos} :
    ofReplaceStart (s.replaceStart pos).startPos = pos :=
  Slice.Pos.ext (by simp)

@[simp]
theorem Slice.Pos.ofReplaceStart_endPos {s : Slice} {pos : s.Pos} :
    ofReplaceStart (s.replaceStart pos).endPos = s.endPos := by
  have := pos.isValidForSlice.le_rawEndPos
  simp_all [Pos.ext_iff, String.Pos.Raw.ext_iff, Pos.Raw.le_iff]

theorem Slice.Pos.ofReplaceStart_inj {s : Slice} {p₀ : s.Pos} {pos pos' : (s.replaceStart p₀).Pos} :
    ofReplaceStart pos = ofReplaceStart pos' ↔ pos = pos' := by
  simp [Pos.ext_iff, String.Pos.Raw.ext_iff]

theorem Slice.Pos.get_eq_get_ofReplaceStart {s : Slice} {p₀ : s.Pos} {pos : (s.replaceStart p₀).Pos} {h} :
    pos.get h = (ofReplaceStart pos).get (by rwa [← ofReplaceStart_endPos, ne_eq, ofReplaceStart_inj]) := by
  simp [Slice.Pos.get, Nat.add_assoc]

/-- Given a position in `s.replaceEnd p₀`, obtain the corresponding position in `s`. -/
@[inline]
def Slice.Pos.ofReplaceEnd {s : Slice} {p₀ : s.Pos} (pos : (s.replaceEnd p₀).Pos) : s.Pos where
  offset := pos.offset
  isValidForSlice := (Pos.Raw.isValidForSlice_replaceEnd.1 pos.isValidForSlice).2

@[simp]
theorem Slice.Pos.offset_ofReplaceEnd {s : Slice} {p₀ : s.Pos} {pos : (s.replaceEnd p₀).Pos} :
    (ofReplaceEnd pos).offset = pos.offset := (rfl)

/-- Given a position in `s` that is at most `p₀`, obtain the corresponding position in `s.replaceEnd p₀`. -/
@[inline]
def Slice.Pos.toReplaceEnd {s : Slice} (p₀ : s.Pos) (pos : s.Pos) (h : pos ≤ p₀) :
    (s.replaceEnd p₀).Pos where
  offset := pos.offset
  isValidForSlice := Pos.Raw.isValidForSlice_replaceEnd.2 ⟨h, pos.isValidForSlice⟩

@[simp]
theorem Slice.Pos.offset_toReplaceEnd {s : Slice} {p₀ : s.Pos} {pos : s.Pos} {h : pos ≤ p₀} :
    (toReplaceEnd p₀ pos h).offset = pos.offset := (rfl)

theorem Slice.Pos.copy_eq_append_get {s : Slice} {pos : s.Pos} (h : pos ≠ s.endPos) :
    ∃ t₁ t₂ : String, s.copy = t₁ ++ singleton (pos.get h) ++ t₂ ∧ t₁.utf8ByteSize = pos.offset.byteIdx := by
  obtain ⟨t₂, ht₂⟩ := (s.replaceStart pos).copy.eq_singleton_append (by simpa [← ValidPos.ofCopy_inj, ← ofReplaceStart_inj])
  refine ⟨(s.replaceEnd pos).copy, t₂, ?_, by simp⟩
  simp only [Slice.startValidPos_copy, get_toCopy, get_eq_get_ofReplaceStart, ofReplaceStart_startPos] at ht₂
  rw [append_assoc, ← ht₂, ← copy_eq_copy_replaceEnd]

theorem Slice.Pos.utf8ByteSize_byte {s : Slice} {pos : s.Pos} {h : pos ≠ s.endPos} :
    (pos.byte h).utf8ByteSize pos.isUTF8FirstByte_byte = (pos.get h).utf8Size := by
  simp [getUTF8Byte, byte, String.getUTF8Byte, get_eq_utf8DecodeChar, ByteArray.utf8Size_utf8DecodeChar]

theorem ValidPos.utf8ByteSize_byte {s : String} {pos : s.ValidPos} {h : pos ≠ s.endValidPos} :
    (pos.byte h).utf8ByteSize pos.isUTF8FirstByte_byte = (pos.get h).utf8Size :=
  Slice.Pos.utf8ByteSize_byte

/-- Advances a valid position on a slice to the next valid position, given a proof that the
position is not the past-the-end position, which guarantees that such a position exists. -/
@[expose]
def Slice.Pos.next {s : Slice} (pos : s.Pos) (h : pos ≠ s.endPos) : s.Pos where
  offset := pos.offset.increaseBy ((pos.byte h).utf8ByteSize pos.isUTF8FirstByte_byte)
  isValidForSlice := by
    obtain ⟨t₁, t₂, ht, ht'⟩ := copy_eq_append_get h
    replace ht' : pos.offset = t₁.rawEndPos := Eq.symm (String.Pos.Raw.ext ht')
    rw [utf8ByteSize_byte, ← Pos.Raw.isValid_copy_iff, ht, ht']
    refine Pos.Raw.IsValid.append_right ?_ t₂
    rw [Pos.Raw.increaseBy_charUtf8Size]
    refine Pos.Raw.IsValid.append_left ?_ t₁
    exact Pos.Raw.isValid_singleton.2 (Or.inr rfl)

/-- Advances a valid position on a slice to the next valid position, or returns `none` if the
given position is the past-the-end position. -/
@[expose]
def Slice.Pos.next? {s : Slice} (pos : s.Pos) : Option s.Pos :=
  if h : pos = s.endPos then none else some (pos.next h)

/-- Advances a valid position on a slice to the next valid position, or panics if the given
position is the past-the-end position. -/
@[expose]
def Slice.Pos.next! {s : Slice} (pos : s.Pos) : s.Pos :=
  if h : pos = s.endPos then panic! "Cannot advance the end position" else pos.next h

@[simp]
theorem Slice.Pos.offset_next {s : Slice} {pos : s.Pos} {h : pos ≠ s.endPos} :
    (pos.next h).offset = pos.offset + pos.get h := by
  ext
  simp [next, utf8ByteSize_byte]

theorem Slice.Pos.byteIdx_offset_next {s : Slice} {pos : s.Pos} {h : pos ≠ s.endPos} :
    (pos.next h).offset.byteIdx = pos.offset.byteIdx + (pos.get h).utf8Size := by
  simp

@[simp]
theorem Slice.Pos.lt_next {s : Slice} {pos : s.Pos} {h : pos ≠ s.endPos} :
    pos < pos.next h := by
  simp [Pos.lt_iff, Pos.Raw.lt_iff, Char.utf8Size_pos]

@[inline, expose]
def Slice.Pos.prevAux {s : Slice} (pos : s.Pos) (h : pos ≠ s.startPos) : String.Pos.Raw :=
  go (pos.offset.byteIdx - 1) (by
    have := pos.isValidForSlice.le_rawEndPos
    simp [Pos.Raw.le_iff, Pos.ext_iff] at ⊢ this h
    omega)
where
  go (off : Nat) (h₁ : off < s.utf8ByteSize) : String.Pos.Raw :=
    if hbyte : (s.getUTF8Byte ⟨off⟩ h₁).IsUTF8FirstByte then
      ⟨off⟩
    else
      have : 0 ≠ off := by
        intro h
        obtain hoff : (⟨off⟩ : String.Pos.Raw) = 0 := by simpa [String.Pos.Raw.ext_iff] using h.symm
        simp [hoff, s.isUTF8FirstByte_utf8ByteAt_zero] at hbyte
      match off with
      | 0 => False.elim (by contradiction)
      | off + 1 => go off (by omega)
  termination_by structural off

theorem Pos.Raw.isValidForSlice_prevAuxGo {s : Slice} (off : Nat) (h₁ : off < s.utf8ByteSize) :
    (Slice.Pos.prevAux.go off h₁).IsValidForSlice s := by
  induction off with
  | zero =>
    rw [Slice.Pos.prevAux.go]
    split
    · exact Pos.Raw.isValidForSlice_iff_isUTF8FirstByte.2 (Or.inr ⟨_, ‹_›⟩)
    · simpa using elim
  | succ off ih =>
    rw [Slice.Pos.prevAux.go]
    split
    · exact Pos.Raw.isValidForSlice_iff_isUTF8FirstByte.2 (Or.inr ⟨_, ‹_›⟩)
    · simpa using ih _
where
  elim {P : Pos.Raw → Prop} {h : False} : P h.elim := h.elim

theorem Pos.Raw.isValidForSlice_prevAux {s : Slice} (pos : s.Pos) (h : pos ≠ s.startPos) :
    (pos.prevAux h).IsValidForSlice s :=
  isValidForSlice_prevAuxGo ..

/-- Returns the previous valid position before the given position, given a proof that the position
is not the start position, which guarantees that such a position exists. -/
@[inline, expose]
def Slice.Pos.prev {s : Slice} (pos : s.Pos) (h : pos ≠ s.startPos) : s.Pos where
  offset := prevAux pos h
  isValidForSlice := Pos.Raw.isValidForSlice_prevAux _ _

/-- Returns the previous valid position before the given position, or `none` if the position is
the start position. -/
@[expose]
def Slice.Pos.prev? {s : Slice} (pos : s.Pos) : Option s.Pos :=
  if h : pos = s.startPos then none else some (pos.prev h)

/-- Returns the previous valid position before the given position, or panics if the position is
the start position. -/
@[expose]
def Slice.Pos.prev! {s : Slice} (pos : s.Pos) : s.Pos :=
  if h : pos = s.startPos then panic! "The start position has no previous position" else pos.prev h

/-- Constructs a valid position on `s` from a position and a proof that it is valid. -/
@[inline, expose]
def Slice.pos (s : Slice) (off : String.Pos.Raw) (h : off.IsValidForSlice s) : s.Pos where
  offset := off
  isValidForSlice := h

@[simp]
theorem Slice.offset_pos {s : Slice} {off h} : (s.pos off h).offset = off := rfl

/-- Constructs a valid position on `s` from a position, returning `none` if the position is not valid. -/
@[expose]
def Slice.pos? (s : Slice) (off : String.Pos.Raw) : Option s.Pos :=
  if h : off.isValidForSlice s then
    some (s.pos off (Pos.Raw.isValidForSlice_eq_true_iff.1 h))
  else
    none

/-- Constructs a valid position `s` from a position, panicking if the position is not valid. -/
@[expose]
def Slice.pos! (s : Slice) (off : String.Pos.Raw) : s.Pos :=
  if h : off.isValidForSlice s then
    s.pos off (Pos.Raw.isValidForSlice_eq_true_iff.1 h)
  else
    panic! "Offset is not at a valid UTF-8 character boundary"

/-- Advances a valid position on a string to the next valid position, given a proof that the
position is not the past-the-end position, which guarantees that such a position exists. -/
@[inline, expose]
def ValidPos.next {s : String} (pos : s.ValidPos) (h : pos ≠ s.endValidPos) : s.ValidPos :=
  (pos.toSlice.next (ne_of_apply_ne Slice.Pos.ofSlice (by simpa))).ofSlice

/-- Advances a valid position on a string to the next valid position, or returns `none` if the
given position is the past-the-end position. -/
@[inline, expose]
def ValidPos.next? {s : String} (pos : s.ValidPos) : Option s.ValidPos :=
  pos.toSlice.next?.map Slice.Pos.ofSlice

/-- Advances a valid position on a string to the next valid position, or panics if the given
position is the past-the-end position. -/
@[inline, expose]
def ValidPos.next! {s : String} (pos : s.ValidPos) : s.ValidPos :=
  pos.toSlice.next!.ofSlice

/-- Returns the previous valid position before the given position, given a proof that the position
is not the start position, which guarantees that such a position exists. -/
@[inline, expose]
def ValidPos.prev {s : String} (pos : s.ValidPos) (h : pos ≠ s.startValidPos) : s.ValidPos :=
  (pos.toSlice.prev (ne_of_apply_ne Slice.Pos.ofSlice (by simpa))).ofSlice

/-- Returns the previous valid position before the given position, or `none` if the position is
the start position. -/
@[inline, expose]
def ValidPos.prev? {s : String} (pos : s.ValidPos) : Option s.ValidPos :=
  pos.toSlice.prev?.map Slice.Pos.ofSlice

/-- Returns the previous valid position before the given position, or panics if the position is
the start position. -/
@[inline, expose]
def ValidPos.prev! {s : String} (pos : s.ValidPos) : s.ValidPos :=
  pos.toSlice.prev!.ofSlice

/-- Constructs a valid position on `s` from a position and a proof that it is valid. -/
@[inline, expose]
def pos (s : String) (off : Pos.Raw) (h : off.IsValid s) : s.ValidPos :=
  (s.toSlice.pos off h.toSlice).ofSlice

/-- Constructs a valid position on `s` from a position, returning `none` if the position is not valid. -/
@[inline, expose]
def pos? (s : String) (off : Pos.Raw) : Option s.ValidPos :=
  (s.toSlice.pos? off).map Slice.Pos.ofSlice

/-- Constructs a valid position `s` from a position, panicking if the position is not valid. -/
@[inline, expose]
def pos! (s : String) (off : Pos.Raw) : s.ValidPos :=
  (s.toSlice.pos! off).ofSlice

/-- Constructs a valid position on `t` from a valid position on `s` and a proof that `s = t`. -/
@[inline]
def Slice.Pos.cast {s t : Slice} (pos : s.Pos) (h : s = t) : t.Pos where
  offset := pos.offset
  isValidForSlice := h ▸ pos.isValidForSlice

@[simp]
theorem Slice.Pos.offset_cast {s t : Slice} {pos : s.Pos} {h : s = t} :
    (pos.cast h).offset = pos.offset := (rfl)

@[simp]
theorem Slice.Pos.cast_rfl {s : Slice} {pos : s.Pos} : pos.cast rfl = pos :=
  Slice.Pos.ext (by simp)

/-- Constructs a valid position on `t` from a valid position on `s` and a proof that `s = t`. -/
@[inline]
def ValidPos.cast {s t : String} (pos : s.ValidPos) (h : s = t) : t.ValidPos where
  offset := pos.offset
  isValid := h ▸ pos.isValid

@[simp]
theorem ValidPos.offset_cast {s t : String} {pos : s.ValidPos} {h : s = t} :
    (pos.cast h).offset = pos.offset := (rfl)

@[simp]
theorem ValidPos.cast_rfl {s : String} {pos : s.ValidPos} : pos.cast rfl = pos :=
  ValidPos.ext (by simp)

/-- Given a byte position within a string slice, obtains the smallest valid position that is
strictly greater than the given byte position. -/
@[inline]
def Slice.findNextPos (offset : String.Pos.Raw) (s : Slice) (_h : offset < s.rawEndPos) : s.Pos :=
  go offset.inc
where
  go (offset : String.Pos.Raw) : s.Pos :=
    if h : offset < s.rawEndPos then
      if h' : (s.getUTF8Byte offset h).IsUTF8FirstByte then
        s.pos offset (Pos.Raw.isValidForSlice_iff_isUTF8FirstByte.2 (Or.inr ⟨_, h'⟩))
      else
        go offset.inc
    else
      s.endPos
  termination_by s.utf8ByteSize - offset.byteIdx
  decreasing_by
    simp only [Pos.Raw.lt_iff, byteIdx_rawEndPos, utf8ByteSize_eq, Pos.Raw.byteIdx_inc] at h ⊢
    omega

private theorem Slice.le_offset_findNextPosGo {s : Slice} {o : String.Pos.Raw} (h : o ≤ s.rawEndPos) :
    o ≤ (findNextPos.go s o).offset := by
  fun_induction findNextPos.go with
  | case1 => simp
  | case2 x h₁ h₂ ih =>
    refine Pos.Raw.le_of_lt (Pos.Raw.lt_of_lt_of_le Pos.Raw.lt_inc (ih ?_))
    rw [Pos.Raw.le_iff, Pos.Raw.byteIdx_inc]
    exact Nat.succ_le.2 h₁
  | case3 x h => exact h

theorem Slice.lt_offset_findNextPos {s : Slice} {o : String.Pos.Raw} (h) : o < (s.findNextPos o h).offset :=
  Pos.Raw.lt_of_lt_of_le Pos.Raw.lt_inc (le_offset_findNextPosGo (Pos.Raw.inc_le.2 h))

theorem Slice.Pos.prevAuxGo_le_self {s : Slice} {p : Nat} {h : p < s.utf8ByteSize} :
    prevAux.go p h ≤ ⟨p⟩ := by
  induction p with
  | zero =>
    rw [prevAux.go]
    split
    · simp
    · simpa using elim (· ≤ { })
  | succ p ih =>
    rw [prevAux.go]
    split
    · simp
    · simpa using Nat.le_trans ih (by simp)
where
  elim (P : String.Pos.Raw → Prop) {h : False} : P h.elim := h.elim

theorem Slice.Pos.prevAux_lt_self {s : Slice} {p : s.Pos} {h} : p.prevAux h < p.offset := by
  rw [prevAux]
  refine Pos.Raw.lt_of_le_of_lt prevAuxGo_le_self ?_
  simp [Pos.ext_iff, Pos.Raw.lt_iff] at *
  omega

theorem Slice.Pos.prevAux_lt_rawEndPos {s : Slice} {p : s.Pos} {h} : p.prevAux h < s.rawEndPos :=
  Pos.Raw.lt_of_lt_of_le prevAux_lt_self p.isValidForSlice.le_rawEndPos

@[simp]
theorem Slice.Pos.prev_ne_endPos {s : Slice} {p : s.Pos} {h} : p.prev h ≠ s.endPos := by
  simpa [Pos.ext_iff, prev] using Pos.Raw.ne_of_lt prevAux_lt_rawEndPos

@[simp]
theorem ValidPos.prev_ne_endValidPos {s : String} {p : s.ValidPos} {h} : p.prev h ≠ s.endValidPos :=
  mt (congrArg (·.toSlice)) (Slice.Pos.prev_ne_endPos (h := mt (congrArg (·.ofSlice)) h))

theorem ValidPos.toSlice_prev {s : String} {p : s.ValidPos} {h} :
    (p.prev h).toSlice = p.toSlice.prev (ne_of_apply_ne Slice.Pos.ofSlice (by simpa)) := by
  simp [prev]

theorem Slice.Pos.offset_prev_lt_offset {s : Slice} {p : s.Pos} {h} : (p.prev h).offset < p.offset := by
  simpa [prev] using prevAux_lt_self

@[simp]
theorem Slice.Pos.prev_lt {s : Slice} {p : s.Pos} {h} : p.prev h < p :=
  lt_iff.2 offset_prev_lt_offset

@[simp]
theorem ValidPos.prev_lt {s : String} {p : s.ValidPos} {h} : p.prev h < p := by
  simp [← toSlice_lt, toSlice_prev]

/-- Advances the position `p` `n` times, saturating at `s.endPos` if necessary. -/
def Slice.Pos.nextn {s : Slice} (p : s.Pos) (n : Nat) : s.Pos :=
  match n with
  | 0 => p
  | n + 1 =>
    if h : p ≠ s.endPos then
      nextn (p.next h) n
    else
      p

/-- Iterates `p.prev` `n` times, saturating at `s.startPos` if necessary. -/
def Slice.Pos.prevn {s : Slice} (p : s.Pos) (n : Nat) : s.Pos :=
  match n with
  | 0 => p
  | n + 1 =>
    if h : p ≠ s.startPos then
      prevn (p.prev h) n
    else
      p

@[expose]
def Pos.Raw.utf8GetAux : List Char → Pos.Raw → Pos.Raw → Char
  | [],    _, _ => default
  | c::cs, i, p => if i = p then c else utf8GetAux cs (i + c) p

@[deprecated Pos.Raw.utf8GetAux (since := "2025-10-09")]
abbrev utf8GetAux : List Char → Pos.Raw → Pos.Raw → Char :=
  Pos.Raw.utf8GetAux

/--
Returns the character at position `p` of a string. If `p` is not a valid position, returns the
fallback value `(default : Char)`, which is `'A'`, but does not panic.

This function is overridden with an efficient implementation in runtime code. See
`String.Pos.Raw.utf8GetAux` for the reference implementation.

This is a legacy function. The recommended alternative is `String.ValidPos.get`, combined with
`String.pos` or another means of obtaining a `String.ValidPos`.

Examples:
* `"abc".get ⟨1⟩ = 'b'`
* `"abc".get ⟨3⟩ = (default : Char)` because byte `3` is at the end of the string.
* `"L∃∀N".get ⟨2⟩ = (default : Char)` because byte `2` is in the middle of `'∃'`.
-/
@[extern "lean_string_utf8_get", expose]
def Pos.Raw.get (s : @& String) (p : @& Pos.Raw) : Char :=
  utf8GetAux s.data 0 p

@[extern "lean_string_utf8_get", expose, deprecated Pos.Raw.get (since := "2025-10-14")]
def get (s : @& String) (p : @& Pos.Raw) : Char :=
  Pos.Raw.utf8GetAux s.data 0 p

@[expose]
def Pos.Raw.utf8GetAux? : List Char → Pos.Raw → Pos.Raw → Option Char
  | [],    _, _ => none
  | c::cs, i, p => if i = p then some c else utf8GetAux? cs (i + c) p

@[deprecated Pos.Raw.utf8GetAux (since := "2025-10-09")]
abbrev utf8GetAux? : List Char → Pos.Raw → Pos.Raw → Option Char :=
  Pos.Raw.utf8GetAux?

/--
Returns the character at position `p` of a string. If `p` is not a valid position, returns `none`.

This function is overridden with an efficient implementation in runtime code. See
`String.utf8GetAux?` for the reference implementation.

This is a legacy function. The recommended alternative is `String.ValidPos.get`, combined with
`String.pos?` or another means of obtaining a `String.ValidPos`.

Examples:
* `"abc".get? ⟨1⟩ = some 'b'`
* `"abc".get? ⟨3⟩ = none`
* `"L∃∀N".get? ⟨1⟩ = some '∃'`
* `"L∃∀N".get? ⟨2⟩ = none`
-/
@[extern "lean_string_utf8_get_opt", expose]
def Pos.Raw.get? : (@& String) → (@& Pos.Raw) → Option Char
  | s, p => utf8GetAux? s.data 0 p

@[extern "lean_string_utf8_get_opt", expose, deprecated Pos.Raw.get? (since := "2025-10-14")]
def get? : (@& String) → (@& Pos.Raw) → Option Char
  | s, p => Pos.Raw.utf8GetAux? s.data 0 p

/--
Returns the character at position `p` of a string. Panics if `p` is not a valid position.

See `String.pos?` and `String.ValidPos.get` for a safer alternative.

This function is overridden with an efficient implementation in runtime code. See
`String.utf8GetAux` for the reference implementation.

This is a legacy function. The recommended alternative is `String.ValidPos.get`, combined with
`String.pos!` or another means of obtaining a `String.ValidPos`.

Examples
* `"abc".get! ⟨1⟩ = 'b'`
-/
@[extern "lean_string_utf8_get_bang", expose]
def Pos.Raw.get! (s : @& String) (p : @& Pos.Raw) : Char :=
  match s with
  | s => Pos.Raw.utf8GetAux s.data 0 p

@[extern "lean_string_utf8_get_bang", expose, deprecated Pos.Raw.get! (since := "2025-10-14")]
def get! (s : @& String) (p : @& Pos.Raw) : Char :=
  match s with
  | s => Pos.Raw.utf8GetAux s.data 0 p

@[expose]
def Pos.Raw.utf8SetAux (c' : Char) : List Char → Pos.Raw → Pos.Raw → List Char
  | [],    _, _ => []
  | c::cs, i, p =>
    if i = p then (c'::cs) else c::(utf8SetAux c' cs (i + c) p)

@[deprecated Pos.Raw.utf8SetAux (since := "2025-10-09")]
abbrev utf8SetAux (c' : Char) : List Char → Pos.Raw → Pos.Raw → List Char :=
  Pos.Raw.utf8SetAux c'

@[simp]
theorem ValidPos.toSlice_get {s : String} {p : s.ValidPos} {h} :
    p.toSlice.get h = p.get (ne_of_apply_ne (·.toSlice) (by simp_all)) := by
  rfl

@[simp]
theorem ValidPos.offset_next {s : String} (p : s.ValidPos) (h : p ≠ s.endValidPos) :
    (p.next h).offset = p.offset + p.get h := by
  simp [next]

theorem ValidPos.byteIdx_offset_next {s : String} (p : s.ValidPos) (h : p ≠ s.endValidPos) :
    (p.next h).offset.byteIdx = p.offset.byteIdx + (p.get h).utf8Size := by
  simp

theorem ValidPos.toSlice_next {s : String} {p : s.ValidPos} {h} :
    (p.next h).toSlice = p.toSlice.next (ne_of_apply_ne Slice.Pos.ofSlice (by simpa)) := by
  simp [next]

theorem ValidPos.byteIdx_lt_utf8ByteSize {s : String} (p : s.ValidPos) (h : p ≠ s.endValidPos) :
    p.offset.byteIdx < s.utf8ByteSize := by
  have := byteIdx_rawEndPos ▸ Pos.Raw.le_iff.1 p.isValid.le_rawEndPos
  simp only [ne_eq, ValidPos.ext_iff, offset_endValidPos, Pos.Raw.ext_iff, byteIdx_rawEndPos] at h
  omega

@[simp]
theorem ValidPos.lt_next {s : String} (p : s.ValidPos) {h} : p < p.next h := by
  simp [← ValidPos.toSlice_lt, toSlice_next]

@[simp]
theorem ValidPos.str_toSlice {s : String} {p : s.ValidPos} : p.toSlice.str = p := by
  ext
  simp

/-- The slice from the beginning of `s` up to `p` (exclusive). -/
@[inline, expose]
def replaceEnd (s : String) (p : s.ValidPos) : Slice :=
  s.toSlice.replaceEnd p.toSlice

@[simp]
theorem str_replaceEnd {s : String} {p : s.ValidPos} : (s.replaceEnd p).str = s := rfl

@[simp]
theorem startInclusive_replaceEnd {s : String} {p : s.ValidPos} :
    (s.replaceEnd p).startInclusive = s.startValidPos := by
  simp [replaceEnd]

@[simp]
theorem endExclusive_replaceEnd {s : String} {p : s.ValidPos} :
    (s.replaceEnd p).endExclusive = p := by
  simp [replaceEnd]

@[simp]
theorem rawEndPos_replaceEnd {s : String} {p : s.ValidPos} :
    (s.replaceEnd p).rawEndPos = p.offset := by
  simp [replaceEnd]

theorem Pos.Raw.isValidForSlice_stringReplaceEnd {s : String} {p : s.ValidPos} {q : Pos.Raw} :
    q.IsValidForSlice (s.replaceEnd p) ↔ q ≤ p.offset ∧ q.IsValid s := by
  rw [replaceEnd, isValidForSlice_replaceEnd, ValidPos.offset_toSlice, isValidForSlice_toSlice_iff]

/-- The slice from `p` (inclusive) up to the end of `s`. -/
@[inline, expose]
def replaceStart (s : String) (p : s.ValidPos) : Slice :=
  s.toSlice.replaceStart p.toSlice

@[simp]
theorem str_replaceStart {s : String} {p : s.ValidPos} : (s.replaceStart p).str = s := rfl

@[simp]
theorem startInclusive_replaceStart {s : String} {p : s.ValidPos} :
    (s.replaceStart p).startInclusive = p := by
  simp [replaceStart]

@[simp]
theorem endExclusive_replaceStart {s : String} {p : s.ValidPos} :
    (s.replaceStart p).endExclusive = s.endValidPos := by
  simp [replaceStart]

theorem Pos.Raw.isValidForSlice_stringReplaceStart {s : String} {p : s.ValidPos} {q : Pos.Raw} :
    q.IsValidForSlice (s.replaceStart p) ↔ (q.offsetBy p.offset).IsValid s := by
  rw [replaceStart, isValidForSlice_replaceStart, isValidForSlice_toSlice_iff,
    ValidPos.offset_toSlice]


/--
Returns the next position in a string after position `p`. If `p` is not a valid position or
`p = s.endPos`, returns the position one byte after `p`.

A run-time bounds check is performed to determine whether `p` is at the end of the string. If a
bounds check has already been performed, use `String.next'` to avoid a repeated check.

This is a legacy function. The recommended alternative is `String.ValidPos.next` or one of its
variants like `String.ValidPos.next?`, combined with `String.pos` or another means of obtaining
a `String.ValisPos`.

Some examples of edge cases:
* `"abc".next ⟨3⟩ = ⟨4⟩`, since `3 = "abc".endPos`
* `"L∃∀N".next ⟨2⟩ = ⟨3⟩`, since `2` points into the middle of a multi-byte UTF-8 character

Examples:
* `"abc".get ("abc".next 0) = 'b'`
* `"L∃∀N".get (0 |> "L∃∀N".next |> "L∃∀N".next) = '∀'`
-/
@[extern "lean_string_utf8_next", expose]
def Pos.Raw.next (s : @& String) (p : @& Pos.Raw) : Pos.Raw :=
  let c := get s p
  p + c

@[extern "lean_string_utf8_next", expose, deprecated Pos.Raw.next (since := "2025-10-14")]
def next (s : @& String) (p : @& Pos.Raw) : Pos.Raw :=
  let c := p.get s
  p + c

@[expose]
def Pos.Raw.utf8PrevAux : List Char → Pos.Raw → Pos.Raw → Pos.Raw
  | [],    _, p => ⟨p.byteIdx - 1⟩
  | c::cs, i, p =>
    let i' := i + c
    if p ≤ i' then i else utf8PrevAux cs i' p

@[deprecated Pos.Raw.utf8PrevAux (since := "2025-10-10")]
abbrev utf8PrevAux : List Char → Pos.Raw → Pos.Raw → Pos.Raw :=
  Pos.Raw.utf8PrevAux

/--
Returns the position in a string before a specified position, `p`. If `p = ⟨0⟩`, returns `0`. If `p`
is greater than `rawEndPos`, returns the position one byte before `p`. Otherwise, if `p` occurs in the
middle of a multi-byte character, returns the beginning position of that character.

For example, `"L∃∀N".prev ⟨3⟩` is `⟨1⟩`, since byte 3 occurs in the middle of the multi-byte
character `'∃'` that starts at byte 1.

This is a legacy function. The recommended alternative is `String.ValidPos.prev` or one of its
variants like `String.ValidPos.prev?`, combined with `String.pos` or another means of obtaining
a `String.ValidPos`.

Examples:
* `"abc".get ("abc".rawEndPos |> "abc".prev) = 'c'`
* `"L∃∀N".get ("L∃∀N".rawEndPos |> "L∃∀N".prev |> "L∃∀N".prev |> "L∃∀N".prev) = '∃'`
-/
@[extern "lean_string_utf8_prev", expose]
def Pos.Raw.prev : (@& String) → (@& Pos.Raw) → Pos.Raw
  | s, p => utf8PrevAux s.data 0 p

@[extern "lean_string_utf8_prev", expose, deprecated Pos.Raw.prev (since := "2025-10-14")]
def prev : (@& String) → (@& Pos.Raw) → Pos.Raw
  | s, p => Pos.Raw.utf8PrevAux s.data 0 p

/--
Returns the first character in `s`. If `s = ""`, returns `(default : Char)`.

Examples:
* `"abc".front = 'a'`
* `"".front = (default : Char)`
-/
@[inline, expose] def front (s : String) : Char :=
  Pos.Raw.get s 0

@[export lean_string_front]
def Internal.frontImpl (s : String) : Char :=
  String.front s

theorem front_eq_get {s : String} : s.front = (0 : Pos.Raw).get s := rfl

/--
Returns the last character in `s`. If `s = ""`, returns `(default : Char)`.

Examples:
* `"abc".back = 'c'`
* `"".back = (default : Char)`
-/
@[inline, expose] def back (s : String) : Char :=
  (s.rawEndPos.prev s).get s

theorem back_eq_get_prev_rawEndPos {s : String} : s.back = (s.rawEndPos.prev s).get s := rfl

@[deprecated back_eq_get_prev_rawEndPos (since := "2025-10-20")]
theorem back_eq_get_prev_endPos {s : String} : s.back = (s.rawEndPos.prev s).get s := rfl

/--
Returns `true` if a specified byte position is greater than or equal to the position which points to
the end of a string. Otherwise, returns `false`.

Examples:
* `(0 |> "abc".next |> "abc".next |> "abc".atEnd) = false`
* `(0 |> "abc".next |> "abc".next |> "abc".next |> "abc".next |> "abc".atEnd) = true`
* `(0 |> "L∃∀N".next |> "L∃∀N".next |> "L∃∀N".next |> "L∃∀N".atEnd) = false`
* `(0 |> "L∃∀N".next |> "L∃∀N".next |> "L∃∀N".next |> "L∃∀N".next |> "L∃∀N".atEnd) = true`
* `"abc".atEnd ⟨4⟩ = true`
* `"L∃∀N".atEnd ⟨7⟩ = false`
* `"L∃∀N".atEnd ⟨8⟩ = true`
-/
@[extern "lean_string_utf8_at_end", expose]
def Pos.Raw.atEnd : (@& String) → (@& Pos.Raw) → Bool
  | s, p => p.byteIdx ≥ utf8ByteSize s

@[extern "lean_string_utf8_at_end", expose, deprecated Pos.Raw.atEnd (since := "2025-10-14")]
def atEnd : (@& String) → (@& Pos.Raw) → Bool
  | s, p => p.byteIdx ≥ utf8ByteSize s

/--
Returns the character at position `p` of a string. Returns `(default : Char)`, which is `'A'`, if
`p` is not a valid position.

Requires evidence, `h`, that `p` is within bounds instead of performing a run-time bounds check as
in `String.get`.

A typical pattern combines `get'` with a dependent `if`-expression to avoid the overhead of an
additional bounds check. For example:
```
def getInBounds? (s : String) (p : String.Pos) : Option Char :=
  if h : s.atEnd p then none else some (s.get' p h)
```
Even with evidence of `¬ s.atEnd p`, `p` may be invalid if a byte index points into the middle of a
multi-byte UTF-8 character. For example, `"L∃∀N".get' ⟨2⟩ (by decide) = (default : Char)`.

This is a legacy function. The recommended alternative is `String.ValidPos.get`, combined with
`String.pos` or another means of obtaining a `String.ValidPos`.

Examples:
* `"abc".get' 0 (by decide) = 'a'`
* `let lean := "L∃∀N"; lean.get' (0 |> lean.next |> lean.next) (by decide) = '∀'`
-/
@[extern "lean_string_utf8_get_fast", expose]
def Pos.Raw.get' (s : @& String) (p : @& Pos.Raw) (h : ¬ p.atEnd s) : Char :=
  match s with
  | s => Pos.Raw.utf8GetAux s.data 0 p

@[extern "lean_string_utf8_get_fast", expose, deprecated Pos.Raw.get' (since := "2025-10-14")]
def get' (s : @& String) (p : @& Pos.Raw) (h : ¬ p.atEnd s) : Char :=
  match s with
  | s => Pos.Raw.utf8GetAux s.data 0 p

/--
Returns the next position in a string after position `p`. The result is unspecified if `p` is not a
valid position.

Requires evidence, `h`, that `p` is within bounds. No run-time bounds check is performed, as in
`String.next`.

A typical pattern combines `String.next'` with a dependent `if`-expression to avoid the overhead of
an additional bounds check. For example:
```
def next? (s : String) (p : String.Pos) : Option Char :=
  if h : s.atEnd p then none else s.get (s.next' p h)
```

This is a legacy function. The recommended alternative is `String.ValidPos.next`, combined with
`String.pos` or another means of obtaining a `String.ValidPos`.

Example:
* `let abc := "abc"; abc.get (abc.next' 0 (by decide)) = 'b'`
-/
@[extern "lean_string_utf8_next_fast", expose]
def Pos.Raw.next' (s : @& String) (p : @& Pos.Raw) (h : ¬ p.atEnd s) : Pos.Raw :=
  let c := p.get s
  p + c

@[extern "lean_string_utf8_next_fast", expose, deprecated Pos.Raw.next' (since := "2025-10-14")]
def next' (s : @& String) (p : @& Pos.Raw) (h : ¬ p.atEnd s) : Pos.Raw :=
  let c := p.get s
  p + c

theorem Pos.Raw.lt_next (s : String) (i : Pos.Raw) : i < i.next s :=
  Nat.add_lt_add_left (Char.utf8Size_pos _) _

theorem Pos.Raw.byteIdx_lt_byteIdx_next (s : String) (i : Pos.Raw) : i.1 < (i.next s).1 :=
  lt_iff.1 (i.lt_next s)

@[deprecated Pos.Raw.byteIdx_lt_byteIdx_next (since := "2025-10-10")]
theorem lt_next (s : String) (i : Pos.Raw) : i.1 < (i.next s).1 :=
  Pos.Raw.lt_next s i

theorem Pos.Raw.utf8PrevAux_lt_of_pos : ∀ (cs : List Char) (i p : Pos.Raw), i < p → p ≠ 0 →
    (Pos.Raw.utf8PrevAux cs i p).1 < p.1
  | [], _, _, _, h => Nat.sub_one_lt (mt (congrArg Pos.Raw.mk) h)
  | c::cs, i, p, h, h' => by
    simp [utf8PrevAux]
    apply iteInduction (motive := (Pos.Raw.byteIdx · < _)) <;> intro h''
    next => exact h
    next => exact utf8PrevAux_lt_of_pos _ _ _ (Nat.lt_of_not_le h'') h'

theorem Pos.Raw.prev_lt_of_pos (s : String) (i : Pos.Raw) (h : i ≠ 0) : (i.prev s).1 < i.1 :=
  utf8PrevAux_lt_of_pos _ _ _ (Nat.zero_lt_of_ne_zero (mt (congrArg Pos.Raw.mk) h)) h

@[deprecated Pos.Raw.prev_lt_of_pos (since := "2025-10-10")]
theorem prev_lt_of_pos (s : String) (i : Pos.Raw) (h : i ≠ 0) : (i.prev s).1 < i.1 :=
  Pos.Raw.prev_lt_of_pos s i h

def posOfAux (s : String) (c : Char) (stopPos : Pos.Raw) (pos : Pos.Raw) : Pos.Raw :=
  if h : pos < stopPos then
    if pos.get s == c then pos
    else
      have := Nat.sub_lt_sub_left h (Pos.Raw.lt_next s pos)
      posOfAux s c stopPos (pos.next s)
  else pos
termination_by stopPos.1 - pos.1

/--
Returns the position of the first occurrence of a character, `c`, in a string `s`. If `s` does not
contain `c`, returns `s.rawEndPos`.

Examples:
* `"abcba".posOf 'a' = ⟨0⟩`
* `"abcba".posOf 'z' = ⟨5⟩`
* `"L∃∀N".posOf '∀' = ⟨4⟩`
-/
@[inline] def posOf (s : String) (c : Char) : Pos.Raw :=
  posOfAux s c s.rawEndPos 0

@[export lean_string_posof]
def Internal.posOfImpl (s : String) (c : Char) : Pos.Raw :=
  String.posOf s c

def revPosOfAux (s : String) (c : Char) (pos : Pos.Raw) : Option Pos.Raw :=
  if h : pos = 0 then none
  else
    have := Pos.Raw.prev_lt_of_pos s pos h
    let pos := pos.prev s
    if pos.get s == c then some pos
    else revPosOfAux s c pos
termination_by pos.1

/--
Returns the position of the last occurrence of a character, `c`, in a string `s`. If `s` does not
contain `c`, returns `none`.

Examples:
* `"abcabc".revPosOf 'a' = some ⟨3⟩`
* `"abcabc".revPosOf 'z' = none`
* `"L∃∀N".revPosOf '∀' = some ⟨4⟩`
-/
@[inline] def revPosOf (s : String) (c : Char) : Option Pos.Raw :=
  revPosOfAux s c s.rawEndPos

def findAux (s : String) (p : Char → Bool) (stopPos : Pos.Raw) (pos : Pos.Raw) : Pos.Raw :=
  if h : pos < stopPos then
    if p (pos.get s) then pos
    else
      have := Nat.sub_lt_sub_left h (Pos.Raw.lt_next s pos)
      findAux s p stopPos (pos.next s)
  else pos
termination_by stopPos.1 - pos.1

/--
Finds the position of the first character in a string for which the Boolean predicate `p` returns
`true`. If there is no such character in the string, then the end position of the string is
returned.

Examples:
 * `"coffee tea water".find (·.isWhitespace) = ⟨6⟩`
 * `"tea".find (· == 'X') = ⟨3⟩`
 * `"".find (· == 'X') = ⟨0⟩`
-/
@[inline] def find (s : String) (p : Char → Bool) : Pos.Raw :=
  findAux s p s.rawEndPos 0

def revFindAux (s : String) (p : Char → Bool) (pos : Pos.Raw) : Option Pos.Raw :=
  if h : pos = 0 then none
  else
    have := Pos.Raw.prev_lt_of_pos s pos h
    let pos := pos.prev s
    if p (pos.get s) then some pos
    else revFindAux s p pos
termination_by pos.1

/--
Finds the position of the last character in a string for which the Boolean predicate `p` returns
`true`. If there is no such character in the string, then `none` is returned.

Examples:
 * `"coffee tea water".revFind (·.isWhitespace) = some ⟨10⟩`
 * `"tea".revFind (· == 'X') = none`
 * `"".revFind (· == 'X') = none`
-/
@[inline] def revFind (s : String) (p : Char → Bool) : Option Pos.Raw :=
  revFindAux s p s.rawEndPos

/--
Returns the first position where the two strings differ.

If one string is a prefix of the other, then the returned position is the end position of the
shorter string. If the strings are identical, then their end position is returned.

Examples:
* `"tea".firstDiffPos "ten" = ⟨2⟩`
* `"tea".firstDiffPos "tea" = ⟨3⟩`
* `"tea".firstDiffPos "teas" = ⟨3⟩`
* `"teas".firstDiffPos "tea" = ⟨3⟩`
-/
@[expose]
def firstDiffPos (a b : String) : Pos.Raw :=
  let stopPos := a.rawEndPos.min b.rawEndPos
  let rec loop (i : Pos.Raw) : Pos.Raw :=
    if h : i < stopPos then
      if i.get a != i.get b then i
      else
        have := Nat.sub_lt_sub_left h (Pos.Raw.lt_next a i)
        loop (i.next a)
    else i
    termination_by stopPos.1 - i.1
  loop 0

/--
Creates a new string that consists of the region of the input string delimited by the two positions.

The result is `""` if the start position is greater than or equal to the end position or if the
start position is at the end of the string. If either position is invalid (that is, if either points
at the middle of a multi-byte UTF-8 character) then the result is unspecified.

This is a legacy function. The recommended alternative is `String.ValidPos.extract`, but usually
it is even better to operate on `String.Slice` instead and call `String.Slice.copy` (only) if
required.

Examples:
* `"red green blue".extract ⟨0⟩ ⟨3⟩ = "red"`
* `"red green blue".extract ⟨3⟩ ⟨0⟩ = ""`
* `"red green blue".extract ⟨0⟩ ⟨100⟩ = "red green blue"`
* `"red green blue".extract ⟨4⟩ ⟨100⟩ = "green blue"`
* `"L∃∀N".extract ⟨1⟩ ⟨2⟩ = "∃∀N"`
* `"L∃∀N".extract ⟨2⟩ ⟨100⟩ = ""`
-/
@[extern "lean_string_utf8_extract", expose]
def Pos.Raw.extract : (@& String) → (@& Pos.Raw) → (@& Pos.Raw) → String
  | s, b, e => if b.byteIdx ≥ e.byteIdx then "" else (go₁ s.data 0 b e).asString
where
  go₁ : List Char → Pos.Raw → Pos.Raw → Pos.Raw → List Char
    | [],        _, _, _ => []
    | s@(c::cs), i, b, e => if i = b then go₂ s i e else go₁ cs (i + c) b e

  go₂ : List Char → Pos.Raw → Pos.Raw → List Char
    | [],    _, _ => []
    | c::cs, i, e => if i = e then [] else c :: go₂ cs (i + c) e

@[extern "lean_string_utf8_extract", expose, deprecated Pos.Raw.extract (since := "2025-10-14")]
def extract : (@& String) → (@& Pos.Raw) → (@& Pos.Raw) → String
  | s, b, e => Pos.Raw.extract s b e

@[specialize] def splitAux (s : String) (p : Char → Bool) (b : Pos.Raw) (i : Pos.Raw) (r : List String) : List String :=
  if h : i.atEnd s then
    let r := (b.extract s i)::r
    r.reverse
  else
    have := Nat.sub_lt_sub_left (Nat.gt_of_not_le (mt decide_eq_true h)) (Pos.Raw.lt_next s _)
    if p (i.get s) then
      let i' := i.next s
      splitAux s p i' i' (b.extract s i :: r)
    else
      splitAux s p b (i.next s) r
termination_by s.rawEndPos.1 - i.1

/--
Splits a string at each character for which `p` returns `true`.

The characters that satisfy `p` are not included in any of the resulting strings. If multiple
characters in a row satisfy `p`, then the resulting list will contain empty strings.

Examples:
* `"coffee tea water".split (·.isWhitespace) = ["coffee", "tea", "water"]`
* `"coffee  tea  water".split (·.isWhitespace) = ["coffee", "", "tea", "", "water"]`
* `"fun x =>\n  x + 1\n".split (· == '\n') = ["fun x =>", "  x + 1", ""]`
-/
@[inline] def splitToList (s : String) (p : Char → Bool) : List String :=
  splitAux s p 0 0 []

@[inline, deprecated splitToList (since := "2025-10-17")]
def split (s : String) (p : Char → Bool) : List String :=
  splitToList s p

/--
Auxiliary for `splitOn`. Preconditions:
* `sep` is not empty
* `b <= i` are indexes into `s`
* `j` is an index into `sep`, and not at the end

It represents the state where we have currently parsed some split parts into `r` (in reverse order),
`b` is the beginning of the string / the end of the previous match of `sep`, and the first `j` bytes
of `sep` match the bytes `i-j .. i` of `s`.
-/
def splitOnAux (s sep : String) (b : Pos.Raw) (i : Pos.Raw) (j : Pos.Raw) (r : List String) : List String :=
  if i.atEnd s then
    let r := (b.extract s i)::r
    r.reverse
  else
    if i.get s == j.get sep then
      let i := i.next s
      let j := j.next sep
      if j.atEnd sep then
        splitOnAux s sep i i 0 (b.extract s (i.unoffsetBy j)::r)
      else
        splitOnAux s sep b i j r
    else
      splitOnAux s sep b ((i.unoffsetBy j).next s) 0 r
termination_by (s.rawEndPos.1 - (j.byteDistance i), sep.rawEndPos.1 - j.1)
decreasing_by
  focus
    rename_i h _ _
    left; exact Nat.sub_lt_sub_left
      (Nat.lt_of_le_of_lt (Nat.sub_le ..) (Nat.gt_of_not_le (mt decide_eq_true h)))
      (Nat.lt_of_le_of_lt (Nat.sub_le ..) (Pos.Raw.lt_next s _))
  focus
    rename_i i₀ j₀ _ eq h'
    rw [show (j₀.next sep).byteDistance (i₀.next s) = j₀.byteDistance i₀ by
      change (_ + Char.utf8Size _) - (_ + Char.utf8Size _) = _
      rw [(beq_iff_eq ..).1 eq, Nat.add_sub_add_right]; rfl]
    right; exact Nat.sub_lt_sub_left
      (Nat.lt_of_le_of_lt (Nat.le_add_right ..) (Nat.gt_of_not_le (mt decide_eq_true h')))
      (Pos.Raw.lt_next sep _)
  focus
    rename_i h _
    left; exact Nat.sub_lt_sub_left
      (Nat.lt_of_le_of_lt (Nat.sub_le ..) (Nat.gt_of_not_le (mt decide_eq_true h)))
      (Pos.Raw.lt_next s _)

/--
Splits a string `s` on occurrences of the separator string `sep`. The default separator is `" "`.

When `sep` is empty, the result is `[s]`. When `sep` occurs in overlapping patterns, the first match
is taken. There will always be exactly `n+1` elements in the returned list if there were `n`
non-overlapping matches of `sep` in the string. The separators are not included in the returned
substrings.

Examples:
* `"here is some text ".splitOn = ["here", "is", "some", "text", ""]`
* `"here is some text ".splitOn "some" = ["here is ", " text "]`
* `"here is some text ".splitOn "" = ["here is some text "]`
* `"ababacabac".splitOn "aba" = ["", "bac", "c"]`
-/
@[inline] def splitOn (s : String) (sep : String := " ") : List String :=
  if sep == "" then [s] else splitOnAux s sep 0 0 0 []


def offsetOfPosAux (s : String) (pos : Pos.Raw) (i : Pos.Raw) (offset : Nat) : Nat :=
  if i >= pos then offset
  else if h : i.atEnd s then
    offset
  else
    have := Nat.sub_lt_sub_left (Nat.gt_of_not_le (mt decide_eq_true h)) (Pos.Raw.lt_next s _)
    offsetOfPosAux s pos (i.next s) (offset+1)
termination_by s.rawEndPos.1 - i.1

/--
Returns the character index that corresponds to the provided position (i.e. UTF-8 byte index) in a
string.

If the position is at the end of the string, then the string's length in characters is returned. If
the position is invalid due to pointing at the middle of a UTF-8 byte sequence, then the character
index of the next character after the position is returned.

Examples:
* `"L∃∀N".offsetOfPos ⟨0⟩ = 0`
* `"L∃∀N".offsetOfPos ⟨1⟩ = 1`
* `"L∃∀N".offsetOfPos ⟨2⟩ = 2`
* `"L∃∀N".offsetOfPos ⟨4⟩ = 2`
* `"L∃∀N".offsetOfPos ⟨5⟩ = 3`
* `"L∃∀N".offsetOfPos ⟨50⟩ = 4`
-/
@[inline] def offsetOfPos (s : String) (pos : Pos.Raw) : Nat :=
  offsetOfPosAux s pos 0 0

@[export lean_string_offsetofpos]
def Internal.offsetOfPosImpl (s : String) (pos : Pos.Raw) : Nat :=
  String.offsetOfPos s pos

@[specialize] def foldlAux {α : Type u} (f : α → Char → α) (s : String) (stopPos : Pos.Raw) (i : Pos.Raw) (a : α) : α :=
  if h : i < stopPos then
    have := Nat.sub_lt_sub_left h (Pos.Raw.lt_next s i)
    foldlAux f s stopPos (i.next s) (f a (i.get s))
  else a
termination_by stopPos.1 - i.1

/--
Folds a function over a string from the left, accumulating a value starting with `init`. The
accumulated value is combined with each character in order, using `f`.

Examples:
 * `"coffee tea water".foldl (fun n c => if c.isWhitespace then n + 1 else n) 0 = 2`
 * `"coffee tea and water".foldl (fun n c => if c.isWhitespace then n + 1 else n) 0 = 3`
 * `"coffee tea water".foldl (·.push ·) "" = "coffee tea water"`
-/
@[inline] def foldl {α : Type u} (f : α → Char → α) (init : α) (s : String) : α :=
  foldlAux f s s.rawEndPos 0 init

@[export lean_string_foldl]
def Internal.foldlImpl (f : String → Char → String) (init : String) (s : String) : String :=
  String.foldl f init s

@[specialize] def foldrAux {α : Type u} (f : Char → α → α) (a : α) (s : String) (i begPos : Pos.Raw) : α :=
  if h : begPos < i then
    have := Pos.Raw.prev_lt_of_pos s i <| mt (congrArg String.Pos.Raw.byteIdx) <|
      Ne.symm <| Nat.ne_of_lt <| Nat.lt_of_le_of_lt (Nat.zero_le _) h
    let i := i.prev s
    let a := f (i.get s) a
    foldrAux f a s i begPos
  else a
termination_by i.1

/--
Folds a function over a string from the right, accumulating a value starting with `init`. The
accumulated value is combined with each character in reverse order, using `f`.

Examples:
 * `"coffee tea water".foldr (fun c n => if c.isWhitespace then n + 1 else n) 0 = 2`
 * `"coffee tea and water".foldr (fun c n => if c.isWhitespace then n + 1 else n) 0 = 3`
 * `"coffee tea water".foldr (fun c s => c.push s) "" = "retaw dna aet eeffoc"`
-/
@[inline] def foldr {α : Type u} (f : Char → α → α) (init : α) (s : String) : α :=
  foldrAux f init s s.rawEndPos 0

@[specialize] def anyAux (s : String) (stopPos : Pos.Raw) (p : Char → Bool) (i : Pos.Raw) : Bool :=
  if h : i < stopPos then
    if p (i.get s) then true
    else
      have := Nat.sub_lt_sub_left h (Pos.Raw.lt_next s i)
      anyAux s stopPos p (i.next s)
  else false
termination_by stopPos.1 - i.1

/--
Checks whether there is a character in a string for which the Boolean predicate `p` returns `true`.

Short-circuits at the first character for which `p` returns `true`.

Examples:
 * `"brown".any (·.isLetter) = true`
 * `"brown".any (·.isWhitespace) = false`
 * `"brown and orange".any (·.isLetter) = true`
 * `"".any (fun _ => false) = false`
-/
@[inline] def any (s : String) (p : Char → Bool) : Bool :=
  anyAux s s.rawEndPos p 0

@[export lean_string_any]
def Internal.anyImpl (s : String) (p : Char → Bool) :=
  String.any s p

/--
Checks whether the Boolean predicate `p` returns `true` for every character in a string.

Short-circuits at the first character for which `p` returns `false`.

Examples:
 * `"brown".all (·.isLetter) = true`
 * `"brown and orange".all (·.isLetter) = false`
 * `"".all (fun _ => false) = true`
-/
@[inline] def all (s : String) (p : Char → Bool) : Bool :=
  !s.any (fun c => !p c)

/--
Checks whether a string contains the specified character.

Examples:
* `"green".contains 'e' = true`
* `"green".contains 'x' = false`
* `"".contains 'x' = false`
-/
@[inline] def contains (s : String) (c : Char) : Bool :=
  s.any (fun a => a == c)

@[export lean_string_contains]
def Internal.containsImpl (s : String) (c : Char) : Bool :=
  String.contains s c

theorem Pos.Raw.utf8SetAux_of_gt (c' : Char) : ∀ (cs : List Char) {i p : Pos.Raw}, i > p → utf8SetAux c' cs i p = cs
  | [],    _, _, _ => rfl
  | c::cs, i, p, h => by
    rw [utf8SetAux, if_neg (mt (congrArg (·.1)) (Ne.symm <| Nat.ne_of_lt h)), utf8SetAux_of_gt c' cs]
    exact Nat.lt_of_lt_of_le h (Nat.le_add_right ..)


/--
Checks whether the string can be interpreted as the decimal representation of a natural number.

A string can be interpreted as a decimal natural number if it is not empty and all the characters in
it are digits.

Use `String.toNat?` or `String.toNat!` to convert such a string to a natural number.

Examples:
 * `"".isNat = false`
 * `"0".isNat = true`
 * `"5".isNat = true`
 * `"05".isNat = true`
 * `"587".isNat = true`
 * `"-587".isNat = false`
 * `" 5".isNat = false`
 * `"2+3".isNat = false`
 * `"0xff".isNat = false`
-/
@[inline] def isNat (s : String) : Bool :=
  !s.isEmpty && s.all (·.isDigit)

/--
Interprets a string as the decimal representation of a natural number, returning it. Returns `none`
if the string does not contain a decimal natural number.

A string can be interpreted as a decimal natural number if it is not empty and all the characters in
it are digits.

Use `String.isNat` to check whether `String.toNat?` would return `some`. `String.toNat!` is an
alternative that panics instead of returning `none` when the string is not a natural number.

Examples:
 * `"".toNat? = none`
 * `"0".toNat? = some 0`
 * `"5".toNat? = some 5`
 * `"587".toNat? = some 587`
 * `"-587".toNat? = none`
 * `" 5".toNat? = none`
 * `"2+3".toNat? = none`
 * `"0xff".toNat? = none`
-/
def toNat? (s : String) : Option Nat :=
  if s.isNat then
    some <| s.foldl (fun n c => n*10 + (c.toNat - '0'.toNat)) 0
  else
    none

/--
Checks whether substrings of two strings are equal. Substrings are indicated by their starting
positions and a size in _UTF-8 bytes_. Returns `false` if the indicated substring does not exist in
either string.

This is a legacy function. The recommended alternative is to construct slices representing the
strings to be compared and use the `BEq` instance of `String.Slice`.
-/
def Pos.Raw.substrEq (s1 : String) (pos1 : String.Pos.Raw) (s2 : String) (pos2 : String.Pos.Raw) (sz : Nat) : Bool :=
  pos1.byteIdx + sz ≤ s1.rawEndPos.byteIdx && pos2.byteIdx + sz ≤ s2.rawEndPos.byteIdx && loop pos1 pos2 { byteIdx := pos1.byteIdx + sz }
where
  loop (off1 off2 stop1 : Pos.Raw) :=
    if _h : off1.byteIdx < stop1.byteIdx then
      let c₁ := off1.get s1
      let c₂ := off2.get s2
      c₁ == c₂ && loop (off1 + c₁) (off2 + c₂) stop1
    else true
  termination_by stop1.1 - off1.1
  decreasing_by
    have := Nat.sub_lt_sub_left _h (Nat.add_lt_add_left c₁.utf8Size_pos off1.1)
    decreasing_tactic

@[deprecated Pos.Raw.substrEq (since := "2025-10-10")]
def substrEq (s1 : String) (pos1 : String.Pos.Raw) (s2 : String) (pos2 : String.Pos.Raw) (sz : Nat) : Bool :=
  Pos.Raw.substrEq s1 pos1 s2 pos2 sz

/--
Checks whether the first string (`p`) is a prefix of the second (`s`).

`String.startsWith` is a version that takes the potential prefix after the string.

Examples:
 * `"red".isPrefixOf "red green blue" = true`
 * `"green".isPrefixOf "red green blue" = false`
 * `"".isPrefixOf "red green blue" = true`
-/
def isPrefixOf (p : String) (s : String) : Bool :=
  Pos.Raw.substrEq p 0 s 0 p.rawEndPos.byteIdx

@[export lean_string_isprefixof]
def Internal.isPrefixOfImpl (p : String) (s : String) : Bool :=
  String.isPrefixOf p s

/--
Returns the position of the beginning of the line that contains the position `pos`.

Lines are ended by `'\n'`, and the returned position is either `0 : String.Pos` or immediately after
a `'\n'` character.
-/
def findLineStart (s : String) (pos : String.Pos.Raw) : String.Pos.Raw :=
  match s.revFindAux (· = '\n') pos with
  | none => 0
  | some n => ⟨n.byteIdx + 1⟩

end String

namespace String

@[ext]
theorem ext {s₁ s₂ : String} (h : s₁.data = s₂.data) : s₁ = s₂ :=
  data_injective h

@[simp] theorem length_empty : "".length = 0 := by simp [← length_data, data_empty]

theorem singleton_eq {c : Char} : String.singleton c = [c].asString := by
  simp [← bytes_inj]

@[simp] theorem data_singleton (c : Char) : (String.singleton c).data = [c] := by
  simp [singleton_eq]

@[simp]
theorem length_singleton {c : Char} : (String.singleton c).length = 1 := by
  simp [← length_data]

@[simp] theorem data_push (c : Char) : (String.push s c).data = s.data ++ [c] := by
  simp [← append_singleton]

@[simp] theorem length_push (c : Char) : (String.push s c).length = s.length + 1 := by
  simp [← length_data]

@[simp] theorem length_pushn (c : Char) (n : Nat) : (pushn s c n).length = s.length + n := by
  rw [pushn_eq_repeat_push]; induction n <;> simp [Nat.repeat, Nat.add_assoc, *]

@[simp] theorem length_append (s t : String) : (s ++ t).length = s.length + t.length := by
  simp [← length_data]

attribute [simp] toList -- prefer `String.data` over `String.toList` in lemmas

theorem lt_iff {s t : String} : s < t ↔ s.data < t.data := .rfl

namespace Pos.Raw

@[simp] theorem get!_eq_get (s : String) (p : Pos.Raw) : p.get! s = p.get s := rfl

@[simp] theorem get'_eq (s : String) (p : Pos.Raw) (h) : get' s p h = get s p := rfl

@[simp] theorem next'_eq (s : String) (p : Pos.Raw) (h) : next' s p h = next s p := rfl

end Pos.Raw

@[deprecated Pos.Raw.get!_eq_get (since := "2025-10-14")]
theorem get!_eq_get (s : String) (p : Pos.Raw) : p.get! s = p.get s := rfl

@[deprecated Pos.Raw.lt_next (since := "2025-10-10")]
theorem lt_next' (s : String) (p : Pos.Raw) : p < p.next s :=
  Pos.Raw.lt_next s p

@[simp] theorem Pos.Raw.prev_zero (s : String) : Pos.Raw.prev s 0 = 0 := by
  rw [Pos.Raw.prev]
  cases s.data <;> simp [utf8PrevAux, Pos.Raw.le_iff]

@[deprecated Pos.Raw.prev_zero (since := "2025-10-10")]
theorem prev_zero (s : String) : (0 : Pos.Raw).prev s = 0 := by
  exact Pos.Raw.prev_zero s

@[deprecated Pos.Raw.get'_eq (since := "2025-10-14")]
theorem get'_eq (s : String) (p : Pos.Raw) (h) : p.get' s h = p.get s := rfl

@[deprecated Pos.Raw.next'_eq (since := "2025-10-14")]
theorem next'_eq (s : String) (p : Pos.Raw) (h) : p.next' s h = p.next s := rfl

-- `toSubstring'` is just a synonym for `toSubstring` without the `@[inline]` attribute
-- so for proving can be unfolded.
attribute [simp] toSubstring'

end String

namespace Char

@[simp] theorem length_toString (c : Char) : c.toString.length = 1 := by
  simp [toString_eq_singleton]

end Char

open String
