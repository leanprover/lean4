/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Mario Carneiro, Markus Himmel
-/
module

prelude
public import Init.Data.String.Decode
public import Init.Data.String.Defs
import Init.Data.ByteArray.Lemmas
import Init.Data.Char.Lemmas
public import Init.Data.Char.Basic
import Init.ByCases
import Init.Data.Array.Bootstrap
import Init.Data.Array.Lemmas
import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Sublist
import Init.Data.List.TakeDrop
import Init.Data.Option.Lemmas
import Init.Omega

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
  simp [← size_toByteArray, List.utf8Encode_singleton]

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
  go 0 #[] (by simp)
where
  @[semireducible]
  go (i : Nat) (acc : Array Char) (hi : i ≤ b.size) : Option (Array Char) :=
    if i < b.size then
      match h : utf8DecodeChar? b i with
      | none => none
      | some c => go (i + c.utf8Size) (acc.push c) (le_size_of_utf8DecodeChar?_eq_some h)
    else
      some acc
  termination_by b.size - i
  decreasing_by have := c.utf8Size_pos; omega

@[expose, extern "lean_string_validate_utf8"]
def ByteArray.validateUTF8 (b : @& ByteArray) : Bool :=
  go 0 (by simp)
where
  @[semireducible]
  go (i : Nat) (hi : i ≤ b.size) : Bool :=
    if hi : i < b.size then
      match h : validateUTF8At b i with
      | false => false
      | true => go (i + b[i].utf8ByteSize (isUTF8FirstByte_of_validateUTF8At h)) ?_
    else
      true
  termination_by b.size - i
  decreasing_by
    have := b[i].utf8ByteSize_pos (isUTF8FirstByte_of_validateUTF8At h); omega
finally
  all_goals rw [ByteArray.validateUTF8At_eq_isSome_utf8DecodeChar?] at h
  · rw [← ByteArray.utf8Size_utf8DecodeChar (h := h)]
    exact add_utf8Size_utf8DecodeChar_le_size

theorem ByteArray.isSome_utf8Decode?Go_eq_validateUTF8Go {b : ByteArray}
    {i : Nat} {acc : Array Char} {hi : i ≤ b.size} :
    (utf8Decode?.go b i acc hi).isSome = validateUTF8.go b i hi := by
  fun_induction utf8Decode?.go with
  | case1 i acc hi h₁ h₂ =>
    unfold validateUTF8.go
    simp only [Option.isSome_none, ↓reduceDIte, Bool.false_eq, h₁]
    split
    · rfl
    · rename_i heq
      simp [validateUTF8At_eq_isSome_utf8DecodeChar?, h₂] at heq
  | case2 i acc hi h₁ c h₂ ih =>
    unfold validateUTF8.go
    simp only [↓reduceDIte, ih, h₁]
    split
    · rename_i heq
      simp [validateUTF8At_eq_isSome_utf8DecodeChar?, h₂] at heq
    · congr
      rw [← ByteArray.utf8Size_utf8DecodeChar (h := by simp [h₂])]
      simp [utf8DecodeChar, h₂]
  | case3 => unfold validateUTF8.go; simp [*]

theorem ByteArray.isSome_utf8Decode?_eq_validateUTF8 {b : ByteArray} :
    b.utf8Decode?.isSome = b.validateUTF8 :=
  b.isSome_utf8Decode?Go_eq_validateUTF8Go

@[simp]
theorem ByteArray.utf8Decode?_empty : ByteArray.empty.utf8Decode? = some #[] := by
  simp [utf8Decode?, utf8Decode?.go]

private theorem ByteArray.isSome_utf8Decode?go_iff {b : ByteArray} {hi : i ≤ b.size} {acc : Array Char} :
    (ByteArray.utf8Decode?.go b i acc hi).isSome ↔ IsValidUTF8 (b.extract i b.size) := by
  fun_induction ByteArray.utf8Decode?.go with
  | case1 i hi acc h₁ h₂ =>
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    rintro ⟨l, hl⟩
    have : l ≠ [] := by
      rintro rfl
      simp at hl
      omega
    rw [← l.cons_head_tail this] at hl
    rw [utf8DecodeChar?_eq_utf8DecodeChar?_extract, hl, List.utf8DecodeChar?_utf8Encode_cons] at h₂
    simp at h₂
  | case2 i acc hi h₁ c h₂ ih =>
    rw [ih]
    have h₂' := h₂
    rw [utf8DecodeChar?_eq_utf8DecodeChar?_extract] at h₂'
    obtain ⟨l, hl⟩ := exists_of_utf8DecodeChar?_eq_some h₂'
    rw [ByteArray.extract_eq_extract_append_extract (i := i) (i + c.utf8Size) (by omega)
      (le_size_of_utf8DecodeChar?_eq_some h₂)] at hl ⊢
    rw [ByteArray.append_inj_left hl (by have := le_size_of_utf8DecodeChar?_eq_some h₂; simp; omega),
      ← List.utf8Encode_singleton, isValidUTF8_utf8Encode_singleton_append_iff]
  | case3 i =>
    have : i = b.size  := by omega
    simp [*]

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
  simp [← String.toByteArray_inj]

@[simp]
theorem String.append_empty {s : String} : s ++ "" = s := by
  simp [← String.toByteArray_inj]

@[simp]
theorem String.ofList_nil : String.ofList [] = "" :=
  rfl

@[deprecated String.ofList_nil (since := "2025-10-30")]
theorem List.asString_nil : String.ofList  [] = "" :=
  String.ofList_nil

@[simp, grind =]
theorem String.ofList_append {l₁ l₂ : List Char} :
    String.ofList (l₁ ++ l₂) = String.ofList l₁ ++ String.ofList l₂ := by
  simp [← String.toByteArray_inj]

@[deprecated String.ofList_append (since := "2025-10-30")]
theorem List.asString_append {l₁ l₂ : List Char} :
    String.ofList (l₁ ++ l₂) = String.ofList l₁ ++ String.ofList l₂ :=
  String.ofList_append

@[expose]
def String.Internal.toArray (b : String) : Array Char :=
  b.toByteArray.utf8Decode?.get (b.toByteArray.isSome_utf8Decode?_iff.2 b.isValidUTF8)

@[simp]
theorem String.Internal.toArray_empty : String.Internal.toArray "" = #[] := by
  simp [toArray]

/--
Converts a string to a list of characters.

Since strings are represented as dynamic arrays of bytes containing the string encoded using
UTF-8, this operation takes time and space linear in the length of the string.

Examples:
 * `"abc".toList = ['a', 'b', 'c']`
 * `"".toList = []`
 * `"\n".toList = ['\n']`
-/
@[extern "lean_string_data", expose]
def String.toList (s : String) : List Char :=
  (String.Internal.toArray s).toList

/--
Converts a string to a list of characters.

Since strings are represented as dynamic arrays of bytes containing the string encoded using
UTF-8, this operation takes time and space linear in the length of the string.

Examples:
 * `"abc".toList = ['a', 'b', 'c']`
 * `"".toList = []`
 * `"\n".toList = ['\n']`
-/
@[extern "lean_string_data", expose, deprecated String.toList (since := "2025-10-30")]
def String.data (b : String) : List Char :=
  (String.Internal.toArray b).toList

@[simp]
theorem String.toList_empty : "".toList = [] := by
  simp [toList]

@[deprecated String.toList_empty (since := "2025-10-30")]
theorem String.data_empty : "".toList = [] :=
  toList_empty

/--
Returns the length of a string in Unicode code points.

Examples:
* `"".length = 0`
* `"abc".length = 3`
* `"L∃∀N".length = 4`
-/
@[extern "lean_string_length", expose, tagged_return]
def String.length (b : @& String) : Nat :=
  b.toList.length

@[simp]
theorem String.Internal.size_toArray {b : String} : (String.Internal.toArray b).size = b.length :=
  (rfl)

@[simp]
theorem String.length_toList {s : String} : s.toList.length = s.length := (rfl)

@[deprecated String.length_toList (since := "2025-10-30")]
theorem String.length_data {b : String} : b.toList.length = b.length := (rfl)

private theorem ByteArray.utf8Decode?go_eq_utf8Decode?go_extract {b : ByteArray} {hi : i ≤ b.size} {acc : Array Char} :
    utf8Decode?.go b i acc hi = (utf8Decode?.go (b.extract i b.size) 0 #[] (by simp)).map (acc ++ ·) := by
  fun_cases utf8Decode?.go b i acc hi with
  | case1 h₁ h₂ =>
    rw [utf8Decode?.go]
    simp only [size_extract, Nat.le_refl, Nat.min_eq_left, Nat.zero_add, List.push_toArray,
      List.nil_append]
    rw [if_pos (by omega)]
    rw [utf8DecodeChar?_eq_utf8DecodeChar?_extract] at h₂
    split <;> simp_all
  | case2 h₁ c h₂ =>
    conv => rhs; rw [utf8Decode?.go]
    simp only [size_extract, Nat.le_refl, Nat.min_eq_left, Nat.zero_add, List.push_toArray,
      List.nil_append]
    rw [if_pos (by omega)]
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
  | case3 =>
      rw [utf8Decode?.go]
      simp only [size_extract, Nat.le_refl, Nat.min_eq_left, Nat.zero_add, List.push_toArray,
        List.nil_append]
      rw [if_neg (by omega)]
      simp
termination_by b.size - i

theorem ByteArray.utf8Decode?_utf8Encode_singleton_append {l : ByteArray} {c : Char} :
    ([c].utf8Encode ++ l).utf8Decode? = l.utf8Decode?.map (#[c] ++ ·) := by
  rw [utf8Decode?, utf8Decode?.go,
    if_pos (by simp [List.utf8Encode_singleton]; have := c.utf8Size_pos; omega)]
  split
  · simp_all [List.utf8DecodeChar?_utf8Encode_singleton_append]
  · rename_i d h
    obtain rfl : c = d := by simpa [List.utf8DecodeChar?_utf8Encode_singleton_append] using h
    rw [utf8Decode?go_eq_utf8Decode?go_extract, utf8Decode?]
    simp only [List.push_toArray, List.nil_append, Nat.zero_add]
    congr 2
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
theorem String.toList_ofList {l : List Char} : (String.ofList l).toList = l := by
  simp [String.toList, String.Internal.toArray]

@[deprecated String.toList_ofList (since := "2025-10-30")]
theorem List.data_asString {l : List Char} : (String.ofList l).toList = l :=
  String.toList_ofList

@[simp]
theorem String.ofList_toList {s : String} : String.ofList s.toList = s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp

@[deprecated String.ofList_toList (since := "2025-10-30")]
theorem String.asString_data {b : String} : String.ofList b.toList = b :=
  String.ofList_toList

@[simp]
theorem String.ofList_comp_toList : String.ofList ∘ String.toList = id := by ext; simp

@[simp]
theorem String.toList_comp_ofList : String.toList ∘ String.ofList = id := by ext; simp

theorem String.ofList_injective {l₁ l₂ : List Char} (h : String.ofList l₁ = String.ofList l₂) : l₁ = l₂ := by
  simpa using congrArg String.toList h

@[deprecated String.ofList_injective (since := "2025-10-30")]
theorem List.asString_injective {l₁ l₂ : List Char} (h : String.ofList l₁ = String.ofList l₂) : l₁ = l₂ :=
  String.ofList_injective h

theorem String.ofList_inj {l₁ l₂ : List Char} : String.ofList l₁ = String.ofList l₂ ↔ l₁ = l₂ :=
  ⟨ofList_injective, (· ▸ rfl)⟩

@[deprecated String.ofList_inj (since := "2025-10-30")]
theorem List.asString_inj {l₁ l₂ : List Char} : String.ofList l₁ = String.ofList l₂ ↔ l₁ = l₂ :=
  String.ofList_inj

theorem String.toList_injective {s₁ s₂ : String} (h : s₁.toList = s₂.toList) : s₁ = s₂ := by
  simpa using congrArg String.ofList h

@[deprecated String.toList_injective (since := "2025-10-30")]
theorem String.data_injective {s₁ s₂ : String} (h : s₁.toList = s₂.toList) : s₁ = s₂ :=
  String.toList_injective h

theorem String.toList_inj {s₁ s₂ : String} : s₁.toList = s₂.toList ↔ s₁ = s₂ :=
  ⟨toList_injective, (· ▸ rfl)⟩

@[deprecated String.toList_inj (since := "2025-10-30")]
theorem String.data_inj {s₁ s₂ : String} : s₁.toList = s₂.toList ↔ s₁ = s₂ :=
  String.toList_inj

@[simp]
theorem String.toList_append {s t : String} : (s ++ t).toList = s.toList ++ t.toList := by
  simp [← String.ofList_inj]

@[deprecated String.toList_append (since := "2025-10-30")]
theorem String.data_append {l₁ l₂ : String} : (l₁ ++ l₂).toList = l₁.toList ++ l₂.toList :=
  String.toList_append

@[simp]
theorem String.utf8Encode_toList {b : String} : b.toList.utf8Encode = b.toByteArray := by
  have := congrArg String.toByteArray (String.ofList_toList (s := b))
  rwa [← String.toByteArray_ofList]

@[deprecated String.utf8Encode_toList (since := "2025-10-30")]
theorem String.utf8encode_data {b : String} : b.toList.utf8Encode = b.toByteArray :=
  String.utf8Encode_toList

@[simp]
theorem String.toList_eq_nil_iff {b : String} : b.toList = [] ↔ b = "" := by
  rw [← String.ofList_inj, ofList_toList, String.ofList_nil]

@[deprecated String.toList_eq_nil_iff (since := "2025-10-30")]
theorem String.data_eq_nil_iff {b : String} : b.toList = [] ↔ b = "" :=
  String.toList_eq_nil_iff

@[simp]
theorem String.ofList_eq_empty_iff {l : List Char} : String.ofList l = "" ↔ l = [] := by
  rw [← String.toList_inj, String.toList_ofList, String.toList_empty]

@[deprecated String.ofList_eq_empty_iff (since := "2025-10-30")]
theorem List.asString_eq_empty_iff {l : List Char} : String.ofList l = "" ↔ l = [] :=
  String.ofList_eq_empty_iff

@[simp]
theorem String.length_ofList {l : List Char} : (String.ofList l).length = l.length := by
  rw [← String.length_toList, String.toList_ofList]

@[deprecated String.length_ofList (since := "2025-10-30")]
theorem List.length_asString {l : List Char} : (String.ofList l).length = l.length :=
  String.length_ofList

end

namespace String

instance : LT String :=
  ⟨fun s₁ s₂ => s₁.toList < s₂.toList⟩

@[extern "lean_string_dec_lt"]
instance decidableLT (s₁ s₂ : @& String) : Decidable (s₁ < s₂) :=
  List.decidableLT s₁.toList s₂.toList

/--
Non-strict inequality on strings, typically used via the `≤` operator.

`a ≤ b` is defined to mean `¬ b < a`.
-/
@[expose, reducible] protected def le (a b : String) : Prop := ¬ b < a

instance : LE String :=
  ⟨String.le⟩

instance decLE (s₁ s₂ : String) : Decidable (s₁ ≤ s₂) :=
  inferInstanceAs (Decidable (Not _))

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
    ∃ m₁ m₂ : List Char, m₁.utf8Encode = s.toByteArray.extract 0 p.byteIdx ∧ String.ofList (m₁ ++ m₂) = s := by
  obtain ⟨l, hl⟩ := s.isValidUTF8
  obtain ⟨m₁, hm₁⟩ := h.isValidUTF8_extract_zero
  suffices m₁ <+: l by
    obtain ⟨m₂, rfl⟩ := this
    refine ⟨m₁, m₂, hm₁.symm, ?_⟩
    apply String.toByteArray_inj.1
    simpa using hl.symm
  apply List.isPrefix_of_utf8Encode_append_eq_utf8Encode (s.toByteArray.extract p.byteIdx s.toByteArray.size)
  rw [← hl, ← hm₁, ← ByteArray.extract_eq_extract_append_extract _ (by simp),
    ByteArray.extract_zero_size]
  simpa using h.le_rawEndPos

theorem Pos.Raw.IsValid.isValidUTF8_extract_utf8ByteSize {s : String} {p : Pos.Raw} (h : p.IsValid s) :
    ByteArray.IsValidUTF8 (s.toByteArray.extract p.byteIdx s.utf8ByteSize) := by
  obtain ⟨m₁, m₂, hm, rfl⟩ := h.exists
  simp only [String.ofList_append, toByteArray_append, String.toByteArray_ofList]
  rw [ByteArray.extract_append_eq_right]
  · exact ByteArray.isValidUTF8_utf8Encode
  · rw [hm]
    simp only [String.ofList_append, toByteArray_append, String.toByteArray_ofList, ByteArray.size_extract,
      ByteArray.size_append, Nat.sub_zero]
    refine (Nat.min_eq_left ?_).symm
    simpa [utf8ByteSize, Pos.Raw.le_iff] using h.le_rawEndPos
  · simp [utf8ByteSize]

theorem Pos.Raw.isValid_iff_exists_append {s : String} {p : Pos.Raw} :
    p.IsValid s ↔ ∃ s₁ s₂ : String, s = s₁ ++ s₂ ∧ p = s₁.rawEndPos := by
  refine ⟨fun h => ⟨⟨_, h.isValidUTF8_extract_zero⟩, ⟨_, h.isValidUTF8_extract_utf8ByteSize⟩, ?_, ?_⟩, ?_⟩
  · apply String.toByteArray_inj.1
    have := Pos.Raw.le_iff.1 h.le_rawEndPos
    simp_all [← size_toByteArray]
  · have := byteIdx_rawEndPos ▸ Pos.Raw.le_iff.1 h.le_rawEndPos
    apply String.Pos.Raw.ext
    simp [Nat.min_eq_left this]
  · rintro ⟨s₁, s₂, rfl, rfl⟩
    refine isValid_iff_isValidUTF8_extract_zero.2 ⟨by simp [Pos.Raw.le_iff], ?_⟩
    simpa [ByteArray.extract_append_eq_left] using s₁.isValidUTF8

theorem Pos.Raw.isValid_ofList {l : List Char} {p : Pos.Raw} :
    p.IsValid (ofList l) ↔ ∃ i, p.byteIdx = (ofList (l.take i)).utf8ByteSize := by
  rw [isValid_iff_exists_append]
  refine ⟨?_, ?_⟩
  · rintro ⟨t₁, t₂, ht, rfl⟩
    refine ⟨t₁.length, ?_⟩
    have := congrArg String.toList ht
    simp only [String.toList_ofList, String.toList_append] at this
    simp [this]
  · rintro ⟨i, hi⟩
    refine ⟨ofList (l.take i), ofList (l.drop i), ?_, ?_⟩
    · simp [← String.ofList_append]
    · simpa [Pos.Raw.ext_iff]

@[deprecated Pos.Raw.isValid_ofList (since := "2025-10-30")]
theorem Pos.Raw.isValid_asString {l : List Char} {p : Pos.Raw} :
    p.IsValid (ofList l) ↔ ∃ i, p.byteIdx = (ofList (l.take i)).utf8ByteSize :=
  Pos.Raw.isValid_ofList

theorem Pos.Raw.isValid_iff_exists_take_toList {s : String} {p : Pos.Raw} :
    p.IsValid s ↔ ∃ i, p.byteIdx = (ofList (s.toList.take i)).utf8ByteSize := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [isValid_ofList]

@[deprecated Pos.Raw.isValid_iff_exists_take_toList (since := "2025-10-30")]
theorem Pos.Raw.isValid_iff_exists_take_data {s : String} {p : Pos.Raw} :
    p.IsValid s ↔ ∃ i, p.byteIdx = (ofList (s.toList.take i)).utf8ByteSize :=
  Pos.Raw.isValid_iff_exists_take_toList

@[simp]
theorem Pos.Raw.isValid_singleton {c : Char} {p : Pos.Raw} :
    p.IsValid (String.singleton c) ↔ p = 0 ∨ p.byteIdx = c.utf8Size := by
  rw [singleton_eq_ofList, Pos.Raw.isValid_ofList]
  refine ⟨?_, ?_⟩
  · rintro ⟨i, hi'⟩
    obtain ⟨rfl, hi⟩ : i = 0 ∨ 1 ≤ i := by omega
    · simp [Pos.Raw.ext_iff, hi']
    · rw [hi', List.take_of_length_le (by simpa)]
      simp [← singleton_eq_ofList]
  · rintro (rfl|hi)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp [hi, ← singleton_eq_ofList]⟩

theorem Pos.Raw.isValid_append {s t : String} {p : Pos.Raw} :
    p.IsValid (s ++ t) ↔ p.IsValid s ∨ (s.rawEndPos ≤ p ∧ (p - s).IsValid t) := by
  obtain ⟨s, rfl⟩ := exists_eq_ofList s
  obtain ⟨t, rfl⟩ := exists_eq_ofList t
  rw [← String.ofList_append, Pos.Raw.isValid_ofList, Pos.Raw.isValid_ofList, Pos.Raw.isValid_ofList]
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
        Nat.add_sub_cancel_left, String.ofList_append, utf8ByteSize_append]
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
  simp [← size_toByteArray, List.utf8Encode_singleton]

@[simp]
theorem rawEndPos_push {s : String} {c : Char} : (s.push c).rawEndPos = s.rawEndPos + c := by
  simp [Pos.Raw.ext_iff]

@[deprecated rawEndPos_push (since := "2025-10-20")]
theorem endPos_push {s : String} {c : Char} : (s.push c).rawEndPos = s.rawEndPos + c :=
  rawEndPos_push

theorem push_induction (s : String) (motive : String → Prop) (empty : motive "")
    (push : ∀ b c, motive b → motive (b.push c)) : motive s := by
  obtain ⟨m, rfl⟩ := s.exists_eq_ofList
  apply append_singleton_induction m (motive <| ofList ·)
  · simpa
  · intro l c hl
    rw [String.ofList_append, ← singleton_eq_ofList, append_singleton]
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
        simp only [getUTF8Byte, toByteArray_push, byteIdx_rawEndPos]
        rw [ByteArray.getElem_append_right (by simp)]
        simp [List.isUTF8FirstByte_getElem_utf8Encode_singleton]
      · refine Or.inr ⟨by simp [lt_iff] at h ⊢; omega, ?_⟩
        simp only [getUTF8Byte, toByteArray_push]
        rwa [ByteArray.getElem_append_left, ← getUTF8Byte]
      · exact Or.inl (by simpa [rawEndPos_push])
    · rintro (h|⟨h, hb⟩)
      · exact Or.inr (by simpa [rawEndPos_push] using h)
      · simp only [getUTF8Byte, toByteArray_push] at hb
        by_cases h' : p < s.rawEndPos
        · refine Or.inl (Or.inr ⟨h', ?_⟩)
          rwa [ByteArray.getElem_append_left h', ← getUTF8Byte] at hb
        · refine Or.inl (Or.inl ?_)
          rw [ByteArray.getElem_append_right (by simp [lt_iff] at h' ⊢; omega)] at hb
          simp only [size_toByteArray, List.isUTF8FirstByte_getElem_utf8Encode_singleton] at hb
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
    p.IsValid s ↔ p = s.rawEndPos ∨ (s.toByteArray.utf8DecodeChar? p.byteIdx).isSome := by
  refine ⟨?_, fun h => h.elim (by rintro rfl; simp) (fun h => ?_)⟩
  · induction s using push_induction with
    | empty => simp [ByteArray.utf8DecodeChar?]
    | push s c ih =>
      simp only [isValid_push, toByteArray_push]
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
      simp only [lt_iff, byteIdx_rawEndPos, gt_iff_lt, ← size_toByteArray]
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

set_option backward.isDefEq.respectTransparency false in
theorem Pos.Raw.isValidUTF8_extract_iff {s : String} (p₁ p₂ : Pos.Raw) (hle : p₁ ≤ p₂) (hle' : p₂ ≤ s.rawEndPos) :
    (s.toByteArray.extract p₁.byteIdx p₂.byteIdx).IsValidUTF8 ↔ p₁ = p₂ ∨ (p₁.IsValid s ∧ p₂.IsValid s) := by
  have hle'' : p₂.byteIdx ≤ s.toByteArray.size := by simpa [le_iff] using hle'
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
    have htb : t.toByteArray = s.toByteArray.extract 0 p₂.byteIdx := rfl
    have ht : p₁.IsValid t := by
      refine isValid_iff_isValidUTF8_extract_zero.2 ⟨?_, ?_⟩
      · simpa [le_iff, t, Nat.min_eq_left hle'', ← size_toByteArray]
      · simpa [htb, ByteArray.extract_extract, Nat.min_eq_left (le_iff.1 hle)] using h₁.isValidUTF8_extract_zero
    simpa [htb, ByteArray.extract_extract, Nat.zero_add, Nat.min_eq_left hle'', ← size_toByteArray]
      using ht.isValidUTF8_extract_utf8ByteSize

theorem Pos.Raw.isValid_iff_isValidUTF8_extract_utf8ByteSize {s : String} {p : Pos.Raw} :
    p.IsValid s ↔ p ≤ s.rawEndPos ∧ (s.toByteArray.extract p.byteIdx s.utf8ByteSize).IsValidUTF8 := by
  refine ⟨fun h => ⟨h.le_rawEndPos, h.isValidUTF8_extract_utf8ByteSize⟩, fun ⟨h₁, h₂⟩ => ?_⟩
  rw [← byteIdx_rawEndPos, isValidUTF8_extract_iff _ _ h₁ (by simp)] at h₂
  obtain (rfl|h₂) := h₂
  · simp
  · exact h₂.1

theorem Pos.isValidUTF8_extract {s : String} (pos₁ pos₂ : s.Pos) :
    (s.toByteArray.extract pos₁.offset.byteIdx pos₂.offset.byteIdx).IsValidUTF8 := by
  by_cases h : pos₁ ≤ pos₂
  · exact (Pos.Raw.isValidUTF8_extract_iff _ _   h pos₂.isValid.le_rawEndPos).2 (Or.inr ⟨pos₁.isValid, pos₂.isValid⟩)
  · rw [ByteArray.extract_eq_empty_iff.2]
    · exact ByteArray.isValidUTF8_empty
    · rw [Nat.min_eq_left]
      · rw [Pos.le_iff, Pos.Raw.le_iff] at h
        omega
      · have := Pos.Raw.le_iff.1 pos₂.isValid.le_rawEndPos
        rwa [size_toByteArray, ← byteIdx_rawEndPos]

/--
Copies a region of a string to a new string.

The region of `s` from `b` (inclusive) to `e` (exclusive) is copied to a newly-allocated `String`.

If `b`'s offset is greater than or equal to that of `e`, then the resulting string is `""`.

If possible, prefer `String.slice`, which avoids the allocation.
-/
@[extern "lean_string_utf8_extract"]
def extract {s : @& String} (b e : @& s.Pos) : String where
  toByteArray := s.toByteArray.extract b.offset.byteIdx e.offset.byteIdx
  isValidUTF8 := b.isValidUTF8_extract e

@[deprecated String.extract (since := "2025-12-01")]
def Pos.extract {s : String} (b e : @& s.Pos) : String :=
  s.extract b e

@[simp]
theorem toByteArray_extract {s : String} {b e : s.Pos} :
    (s.extract b e).toByteArray = s.toByteArray.extract b.offset.byteIdx e.offset.byteIdx := (rfl)

/-- Creates a `String` from a `String.Slice` by copying the bytes. -/
@[inline]
def Slice.copy (s : Slice) : String :=
  s.str.extract s.startInclusive s.endExclusive

theorem Slice.toByteArray_copy {s : Slice} :
    s.copy.toByteArray = s.str.toByteArray.extract s.startInclusive.offset.byteIdx s.endExclusive.offset.byteIdx := (rfl)

theorem Slice.utf8ByteSize_copy_eq_sub {s : Slice} :
    s.copy.utf8ByteSize = s.endExclusive.offset.byteIdx - s.startInclusive.offset.byteIdx:= by
  simp [← size_toByteArray, toByteArray_copy]
  rw [Nat.min_eq_left (by simpa [Pos.Raw.le_iff] using s.endExclusive.isValid.le_rawEndPos)]

@[simp]
theorem Slice.utf8ByteSize_copy {s : Slice} :
    s.copy.utf8ByteSize = s.utf8ByteSize := by
  rw [utf8ByteSize_copy_eq_sub, utf8ByteSize_eq]

@[simp]
theorem Slice.rawEndPos_copy {s : Slice} : s.copy.rawEndPos = s.rawEndPos := by
  simp [Pos.Raw.ext_iff, utf8ByteSize_eq]

@[simp]
theorem copy_toSlice {s : String} : s.toSlice.copy = s := by
  simp [← toByteArray_inj, Slice.toByteArray_copy, ← size_toByteArray]

@[simp]
theorem copy_comp_toSlice : String.Slice.copy ∘ String.toSlice = id := by
  ext; simp

theorem Slice.getUTF8Byte_eq_getUTF8Byte_copy {s : Slice} {p : Pos.Raw} {h : p < s.rawEndPos} :
    s.getUTF8Byte p h = s.copy.getUTF8Byte p (by simpa) := by
  simp [getUTF8Byte, String.getUTF8Byte, toByteArray_copy, ByteArray.getElem_extract]

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
      Pos.le_iff]
    rw [Slice.toByteArray_copy, ByteArray.extract_extract, Nat.add_zero, Nat.min_eq_left (by omega)] at h₂
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
    simp_all only [le_iff, Slice.byteIdx_rawEndPos, Slice.utf8ByteSize_eq, Pos.le_iff]
    rw [Slice.toByteArray_copy, ByteArray.extract_extract, Nat.add_zero, Nat.min_eq_left (by omega)]
    rw [← byteIdx_offsetBy, Pos.Raw.isValidUTF8_extract_iff]
    · exact Or.inr ⟨s.startInclusive.isValid, h₂⟩
    · simp [le_iff]
    · have := s.endExclusive.isValid.le_rawEndPos
      simp_all [le_iff]
      omega

theorem Pos.Raw.isValidForSlice_iff_isUTF8FirstByte {s : Slice} {p : Pos.Raw} :
    p.IsValidForSlice s ↔ (p = s.rawEndPos ∨ (∃ (h : p < s.rawEndPos), (s.getUTF8Byte p h).IsUTF8FirstByte)) := by
  simp [← isValid_copy_iff, isValid_iff_isUTF8FirstByte, Slice.getUTF8Byte_copy]

theorem Pos.Raw.isValidForSlice_iff_exists_append {s : Slice} {p : Pos.Raw} :
    p.IsValidForSlice s ↔ ∃ t₁ t₂, s.copy = t₁ ++ t₂ ∧ p = t₁.rawEndPos := by
  rw [← isValid_copy_iff, isValid_iff_exists_append]

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
    p.IsValidForSlice s ↔ p = s.rawEndPos ∨ (s.copy.toByteArray.utf8DecodeChar? p.byteIdx).isSome := by
  rw [← isValid_copy_iff, isValid_iff_isSome_utf8DecodeChar?, Slice.rawEndPos_copy]

theorem Slice.toByteArray_str_eq {s : Slice} :
    s.str.toByteArray = s.str.toByteArray.extract 0 s.startInclusive.offset.byteIdx ++
      s.copy.toByteArray ++ s.str.toByteArray.extract s.endExclusive.offset.byteIdx s.str.toByteArray.size := by
  rw [toByteArray_copy, ← ByteArray.extract_eq_extract_append_extract, ← ByteArray.extract_eq_extract_append_extract,
    ByteArray.extract_zero_size]
  · simp
  · simpa [Pos.Raw.le_iff] using s.endExclusive.isValid.le_rawEndPos
  · simp
  · simpa [Pos.Raw.le_iff] using s.startInclusive_le_endExclusive

theorem Pos.Raw.isValidForSlice_iff_isSome_utf8DecodeChar? {s : Slice} {p : Pos.Raw} :
    p.IsValidForSlice s ↔ p = s.rawEndPos ∨ (p < s.rawEndPos ∧ (s.str.toByteArray.utf8DecodeChar? (s.startInclusive.offset.byteIdx + p.byteIdx)).isSome) := by
  refine ⟨?_, ?_⟩
  · rw [isValidForSlice_iff_isSome_utf8DecodeChar?_copy]
    rintro (rfl|h)
    · simp
    · refine Or.inr ⟨?_, ?_⟩
      · have := ByteArray.lt_size_of_isSome_utf8DecodeChar? h
        simpa [Pos.Raw.lt_iff] using this
      · rw [ByteArray.utf8DecodeChar?_eq_utf8DecodeChar?_extract] at h
        rw [Slice.toByteArray_str_eq, ByteArray.append_assoc, ByteArray.utf8DecodeChar?_eq_utf8DecodeChar?_extract]
        simp only [ByteArray.size_append, ByteArray.size_extract, Nat.sub_zero, Nat.le_refl,
          Nat.min_eq_left]
        have h' : s.startInclusive.offset.byteIdx ≤ s.str.toByteArray.size := by
          simpa [le_iff] using s.startInclusive.isValid.le_rawEndPos
        rw [Nat.min_eq_left h', ByteArray.extract_append_size_add' (by simp [size_toByteArray ▸ h']),
          ByteArray.extract_append, Nat.add_sub_cancel_left]
        rw [ByteArray.extract_eq_extract_append_extract s.copy.toByteArray.size]
        · rw [ByteArray.append_assoc]
          apply ByteArray.isSome_utf8DecodeChar?_append h
        · have := ByteArray.lt_size_of_isSome_utf8DecodeChar? h
          simp only [size_toByteArray, Slice.utf8ByteSize_copy, ByteArray.size_extract, Nat.le_refl,
            Nat.min_eq_left] at this
          simp only [size_toByteArray, Slice.utf8ByteSize_copy, ge_iff_le]
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
def Slice.Pos.str {s : Slice} (pos : s.Pos) : s.str.Pos where
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
    Pos.Raw.byteIdx_offsetBy, String.Pos.le_iff] at *
  omega

theorem Slice.Pos.offset_le_offset_str {s : Slice} {pos : s.Pos} :
    pos.offset ≤ pos.str.offset := by
  simp [String.Pos.Raw.le_iff]

@[simp]
theorem Slice.Pos.offset_le_offset_endExclusive {s : Slice} {pos : s.Pos} :
    pos.offset ≤ s.endExclusive.offset :=
  Pos.Raw.le_trans offset_le_offset_str offset_str_le_offset_endExclusive

@[simp]
theorem Slice.Pos.startInclusive_le_str {s : Slice} {pos : s.Pos} :
    s.startInclusive ≤ pos.str := by
  simp [String.Pos.le_iff, Pos.Raw.le_iff]

/--
Given a valid position on `s.str` which is within the bounds of the slice `s`, obtains the
corresponding valid position on `s`.
-/
@[inline]
def Slice.Pos.ofStr {s : Slice} (pos : s.str.Pos) (h₁ : s.startInclusive ≤ pos)
    (h₂ : pos ≤ s.endExclusive) : s.Pos where
  offset := pos.offset.unoffsetBy s.startInclusive.offset
  isValidForSlice := by
    refine ⟨?_, Pos.Raw.offsetBy_unoffsetBy_of_le h₁ |>.symm ▸ pos.isValid⟩
    simp [String.Pos.le_iff, Pos.Raw.le_iff, Slice.utf8ByteSize_eq] at *
    omega

@[simp]
theorem Slice.Pos.offset_ofStr {s : Slice} {pos : s.str.Pos} {h₁ h₂} :
    (ofStr pos h₁ h₂).offset = pos.offset.unoffsetBy s.startInclusive.offset := (rfl)

/-- Given a slice and a valid position within the slice, obtain a new slice on the same underlying
string by replacing the start of the slice with the given position. -/
@[inline, expose] -- for the defeq `(s.sliceFrom pos).str = s.str`
def Slice.sliceFrom (s : Slice) (pos : s.Pos) : Slice where
  str := s.str
  startInclusive := pos.str
  endExclusive := s.endExclusive
  startInclusive_le_endExclusive := Pos.offset_str_le_offset_endExclusive

@[deprecated Slice.sliceFrom (since := "2025-11-20")]
def Slice.replaceStart (s : Slice) (pos : s.Pos) : Slice :=
  s.sliceFrom pos

@[simp]
theorem Slice.str_sliceFrom {s : Slice} {pos : s.Pos} :
    (s.sliceFrom pos).str = s.str := rfl

@[simp]
theorem Slice.startInclusive_sliceFrom {s : Slice} {pos : s.Pos} :
    (s.sliceFrom pos).startInclusive = pos.str := rfl

@[simp]
theorem Slice.endExclusive_sliceFrom {s : Slice} {pos : s.Pos} :
    (s.sliceFrom pos).endExclusive = s.endExclusive := rfl

/-- Given a slice and a valid position within the slice, obtain a new slice on the same underlying
string by replacing the end of the slice with the given position. -/
@[inline, expose] -- for the defeq `(s.sliceTo pos).str = s.str`
def Slice.sliceTo (s : Slice) (pos : s.Pos) : Slice where
  str := s.str
  startInclusive := s.startInclusive
  endExclusive := pos.str
  startInclusive_le_endExclusive := by simp [String.Pos.le_iff, String.Pos.Raw.le_iff]

@[deprecated Slice.sliceTo (since := "2025-11-20")]
def Slice.replaceEnd (s : Slice) (pos : s.Pos) : Slice :=
  s.sliceTo pos

@[simp]
theorem Slice.str_sliceTo {s : Slice} {pos : s.Pos} :
    (s.sliceTo pos).str = s.str := rfl

@[simp]
theorem Slice.startInclusive_sliceTo {s : Slice} {pos : s.Pos} :
    (s.sliceTo pos).startInclusive = s.startInclusive := rfl

@[simp]
theorem Slice.endExclusive_sliceTo {s : Slice} {pos : s.Pos} :
    (s.sliceTo pos).endExclusive = pos.str := rfl

/-- Given a slice and two valid positions within the slice, obtain a new slice on the same underlying
string formed by the new bounds. -/
@[inline, expose] -- for the defeq `(s.slice newStart newEnd).str = s.str`
def Slice.slice (s : Slice) (newStart newEnd : s.Pos)
    (h : newStart ≤ newEnd) : Slice where
  str := s.str
  startInclusive := newStart.str
  endExclusive := newEnd.str
  startInclusive_le_endExclusive := by simpa [String.Pos.le_iff, Pos.Raw.le_iff] using h

@[deprecated Slice.slice (since := "2025-11-20")]
def Slice.replaceStartEnd (s : Slice) (newStart newEnd : s.Pos) (h : newStart ≤ newEnd) : Slice :=
  s.slice newStart newEnd h

@[simp]
theorem Slice.str_slice {s : Slice} {newStart newEnd : s.Pos} {h} :
    (s.slice newStart newEnd h).str = s.str := rfl

@[simp]
theorem Slice.startInclusive_slice {s : Slice} {newStart newEnd : s.Pos} {h} :
    (s.slice newStart newEnd h).startInclusive = newStart.str := rfl

@[simp]
theorem Slice.endExclusive_slice {s : Slice} {newStart newEnd : s.Pos} {h} :
    (s.slice newStart newEnd h).endExclusive = newEnd.str := rfl

/-- Given a slice and two valid positions within the slice, obtain a new slice on the same underlying
string formed by the new bounds, or `none` if the given end is strictly less than the given start. -/
def Slice.slice? (s : Slice) (newStart newEnd : s.Pos) : Option Slice :=
  if h : newStart.offset ≤ newEnd.offset then
    some (s.slice newStart newEnd h)
  else
    none

/-- Given a slice and two valid positions within the slice, obtain a new slice on the same underlying
string formed by the new bounds, or panic if the given end is strictly less than the given start. -/
def Slice.slice! (s : Slice) (newStart newEnd : s.Pos) : Slice :=
  if h : newStart ≤ newEnd then
    s.slice newStart newEnd h
  else
    panic! "Starting position must be less than or equal to end position."

@[deprecated Slice.slice! (since := "2025-11-20")]
def Slice.replaceStartEnd! (s : Slice) (newStart newEnd : s.Pos) : Slice :=
  s.slice! newStart newEnd

@[simp]
theorem Slice.utf8ByteSize_sliceFrom {s : Slice} {pos : s.Pos} :
    (s.sliceFrom pos).utf8ByteSize = s.utf8ByteSize - pos.offset.byteIdx := by
  simp only [utf8ByteSize_eq, str_sliceFrom, endExclusive_sliceFrom,
    startInclusive_sliceFrom, Pos.offset_str, Pos.Raw.byteIdx_offsetBy]
  omega

theorem Slice.rawEndPos_sliceFrom {s : Slice} {pos : s.Pos} :
    (s.sliceFrom pos).rawEndPos = s.rawEndPos.unoffsetBy pos.offset := by
  ext
  simp

@[simp]
theorem Slice.utf8ByteSize_sliceTo {s : Slice} {pos : s.Pos} :
    (s.sliceTo pos).utf8ByteSize = pos.offset.byteIdx := by
  simp [utf8ByteSize_eq]

@[simp]
theorem Slice.rawEndPos_sliceTo {s : Slice} {pos : s.Pos} :
    (s.sliceTo pos).rawEndPos = pos.offset := by
  ext
  simp

@[simp]
theorem Slice.utf8ByteSize_slice {s : Slice} {newStart newEnd : s.Pos} {h} :
    (s.slice newStart newEnd h).utf8ByteSize = newStart.offset.byteDistance newEnd.offset := by
  simp [utf8ByteSize_eq, Pos.Raw.byteDistance_eq]
  omega

theorem Pos.Raw.isValidForSlice_sliceFrom {s : Slice} {p : s.Pos} {off : Pos.Raw} :
    off.IsValidForSlice (s.sliceFrom p) ↔ (off.offsetBy p.offset).IsValidForSlice s := by
  refine ⟨fun ⟨h₁, h₂⟩ => ⟨?_, ?_⟩, fun ⟨h₁, h₂⟩ => ⟨?_, ?_⟩⟩
  · have := p.isValidForSlice.le_rawEndPos
    simp_all [le_iff]
    omega
  · simpa [Pos.Raw.offsetBy_assoc] using h₂
  · simp_all [Pos.Raw.le_iff]
    omega
  · simpa [Pos.Raw.offsetBy_assoc] using h₂

theorem Pos.Raw.isValidForSlice_sliceTo {s : Slice} {p : s.Pos} {off : Pos.Raw} :
    off.IsValidForSlice (s.sliceTo p) ↔ off ≤ p.offset ∧ off.IsValidForSlice s := by
  refine ⟨fun ⟨h₁, h₂⟩ => ⟨?_, ?_, ?_⟩, fun ⟨h₁, ⟨h₂, h₃⟩⟩ => ⟨?_, ?_⟩⟩
  · simpa using h₁
  · simp only [Slice.rawEndPos_sliceTo] at h₁
    exact Pos.Raw.le_trans h₁ p.isValidForSlice.le_rawEndPos
  · simpa using h₂
  · simpa using h₁
  · simpa using h₃

@[extern "lean_string_utf8_get_fast", expose]
def decodeChar (s : @& String) (byteIdx : @& Nat) (h : (s.toByteArray.utf8DecodeChar? byteIdx).isSome) : Char :=
  s.toByteArray.utf8DecodeChar byteIdx h

/-- Obtains the character at the given position in the string. -/
@[inline, expose]
def Slice.Pos.get {s : Slice} (pos : s.Pos) (h : pos ≠ s.endPos) : Char :=
  s.str.decodeChar (s.startInclusive.offset.byteIdx + pos.offset.byteIdx)
    ((Pos.Raw.isValidForSlice_iff_isSome_utf8DecodeChar?.1 pos.isValidForSlice).elim (by simp_all [Pos.ext_iff]) (·.2))

theorem Slice.Pos.get_eq_utf8DecodeChar {s : Slice} (pos : s.Pos) (h : pos ≠ s.endPos) :
    pos.get h = s.str.toByteArray.utf8DecodeChar (s.startInclusive.offset.byteIdx + pos.offset.byteIdx)
      ((Pos.Raw.isValidForSlice_iff_isSome_utf8DecodeChar?.1 pos.isValidForSlice).elim (by simp_all [Pos.ext_iff]) (·.2)) := (rfl)

theorem Slice.Pos.utf8Encode_get_eq_extract {s : Slice} (pos : s.Pos) (h : pos ≠ s.endPos) :
    List.utf8Encode [pos.get h] = s.str.toByteArray.extract (s.startInclusive.offset.byteIdx + pos.offset.byteIdx)
      (s.startInclusive.offset.byteIdx + pos.offset.byteIdx + (pos.get h).utf8Size) := by
  rw [get_eq_utf8DecodeChar pos h, List.utf8Encode_singleton, ByteArray.utf8EncodeChar_utf8DecodeChar]

/-- Returns the byte at the given position in the string, or `none` if the position is the end
position. -/
@[expose]
def Slice.Pos.get? {s : Slice} (pos : s.Pos) : Option Char :=
  if h : pos = s.endPos then none else some (pos.get h)

/-- Returns the byte at the given position in the string, or panics if the position is the end
position. -/
@[expose]
def Slice.Pos.get! {s : Slice} (pos : s.Pos) : Char :=
  if h : pos = s.endPos then panic! "Cannot retrieve character at end position" else pos.get h

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
def Pos.toSlice {s : String} (pos : s.Pos) : s.toSlice.Pos where
  offset := pos.offset
  isValidForSlice := pos.isValid.toSlice

@[simp]
theorem Pos.offset_toSlice {s : String} {pos : s.Pos} : pos.toSlice.offset = pos.offset := (rfl)

/-- Given a string `s`, turns a valid position on the slice `s.toSlice` into a valid position on the
string `s`. -/
@[inline, expose]
def Pos.ofToSlice {s : String} (pos : s.toSlice.Pos) : s.Pos where
  offset := pos.offset
  isValid := pos.isValidForSlice.ofSlice

@[simp]
theorem Pos.offset_ofToSlice {s : String} {pos : s.toSlice.Pos} : (ofToSlice pos).offset = pos.offset := (rfl)

@[simp]
theorem rawEndPos_toSlice {s : String} : s.toSlice.rawEndPos = s.rawEndPos := by
  rw [← Slice.rawEndPos_copy, copy_toSlice]

@[simp]
theorem endPos_toSlice {s : String} : s.toSlice.endPos = s.endPos.toSlice :=
  Slice.Pos.ext (by simp)

@[simp]
theorem startPos_toSlice {s : String} : s.toSlice.startPos = s.startPos.toSlice :=
  Slice.Pos.ext (by simp)

@[simp]
theorem Pos.ofToSlice_toSlice {s : String} (pos : s.Pos) : (ofToSlice pos.toSlice) = pos :=
  Pos.ext (by simp)

@[simp]
theorem Slice.Pos.toSlice_ofToSlice {s : String} (pos : s.toSlice.Pos) : (Pos.ofToSlice pos).toSlice = pos :=
  Slice.Pos.ext (by simp)

@[simp]
theorem Pos.toSlice_comp_ofToSlice {s : String} :
    Pos.toSlice ∘ (Pos.ofToSlice (s := s)) = id := by ext; simp

@[simp]
theorem Pos.ofToSlice_comp_toSlice {s : String} :
    Pos.ofToSlice ∘ (toSlice (s := s)) = id := by ext; simp

@[simp]
theorem Pos.toSlice_inj {s : String} {p q : s.Pos} : p.toSlice = q.toSlice ↔ p = q :=
  ⟨fun h => by simpa using congrArg Pos.ofToSlice h, (· ▸ rfl)⟩

@[simp]
theorem Pos.ofToSlice_inj {s : String} {p q : s.toSlice.Pos} : ofToSlice p = ofToSlice q ↔ p = q :=
  ⟨fun h => by simpa using congrArg Pos.toSlice h, (· ▸ rfl)⟩

@[simp]
theorem Pos.toSlice_le {s : String} {p q : s.Pos} : p.toSlice ≤ q.toSlice ↔ p ≤ q := by
  simp [le_iff, Slice.Pos.le_iff]

@[simp]
theorem Pos.ofToSlice_le {s : String} {p q : s.toSlice.Pos} :
    ofToSlice p ≤ ofToSlice q ↔ p ≤ q := by
  simp [le_iff, Slice.Pos.le_iff]

@[simp]
theorem Pos.toSlice_lt {s : String} {p q : s.Pos} : p.toSlice < q.toSlice ↔ p < q := by
  simp [lt_iff, Slice.Pos.lt_iff]

@[simp]
theorem Pos.ofToSlice_lt {s : String} {p q : s.toSlice.Pos} :
    ofToSlice p < ofToSlice q ↔ p < q := by
  simp [lt_iff, Slice.Pos.lt_iff]

/--
Returns the character at the position `pos` of a string, taking a proof that `p` is not the
past-the-end position.

This function is overridden with an efficient implementation in runtime code.

Examples:
* `("abc".pos ⟨1⟩ (by decide)).get (by decide) = 'b'`
* `("L∃∀N".pos ⟨1⟩ (by decide)).get (by decide) = '∃'`
-/
@[inline, expose]
def Pos.get {s : String} (pos : s.Pos) (h : pos ≠ s.endPos) : Char :=
  pos.toSlice.get (ne_of_apply_ne Pos.ofToSlice (by simp [h]))

/--
Returns the character at the position `pos` of a string, or `none` if the position is the
past-the-end position.

This function is overridden with an efficient implementation in runtime code.
-/
@[inline, expose]
def Pos.get? {s : String} (pos : s.Pos) : Option Char :=
  pos.toSlice.get?

/--
Returns the character at the position `pos` of a string, or panics if the position is the
past-the-end position.

This function is overridden with an efficient implementation in runtime code.
-/
@[inline, expose]
def Pos.get! {s : String} (pos : s.Pos) : Char :=
  pos.toSlice.get!

/--
Returns the byte at the position `pos` of a string.
-/
@[inline, expose]
def Pos.byte {s : String} (pos : s.Pos) (h : pos ≠ s.endPos) : UInt8 :=
  pos.toSlice.byte (ne_of_apply_ne Pos.ofToSlice (by simp [h]))

theorem Pos.isUTF8FirstByte_byte {s : String} {pos : s.Pos} {h : pos ≠ s.endPos} :
    (pos.byte h).IsUTF8FirstByte :=
  Slice.Pos.isUTF8FirstByte_byte

@[simp]
theorem startPos_eq_endPos_iff {b : String} : b.startPos = b.endPos ↔ b = "" := by
  simp [← utf8ByteSize_eq_zero_iff, Pos.ext_iff, Eq.comm (b := b.rawEndPos)]

theorem isSome_utf8DecodeChar?_zero {b : String} (hb : b ≠ "") : (b.toByteArray.utf8DecodeChar? 0).isSome := by
  refine (((Pos.Raw.isValid_iff_isSome_utf8DecodeChar? (s := b)).1 Pos.Raw.isValid_zero).elim ?_ id)
  rw [eq_comm, rawEndPos_eq_zero_iff]
  exact fun h => (hb h).elim

theorem head_toList {b : String} {h} :
    b.toList.head h = b.toByteArray.utf8DecodeChar 0 (isSome_utf8DecodeChar?_zero (by simpa using h)) := by
  obtain ⟨l, rfl⟩ := b.exists_eq_ofList
  match l with
  | [] => simp at h
  | c::cs => simp

@[deprecated head_toList (since := "2025-10-30")]
theorem head_data {b : String} {h} :
    b.toList.head h = b.toByteArray.utf8DecodeChar 0 (isSome_utf8DecodeChar?_zero (by simpa using h)) :=
  head_toList

theorem get_startPos {b : String} (h) :
    b.startPos.get h = b.toList.head (by rwa [ne_eq, toList_eq_nil_iff, ← startPos_eq_endPos_iff]) :=
  head_toList.symm

theorem eq_singleton_append {s : String} (h : s.startPos ≠ s.endPos) :
    ∃ t, s = singleton (s.startPos.get h) ++ t := by
  obtain ⟨m, rfl⟩ := s.exists_eq_ofList
  have hm : m ≠ [] := by
    rwa [ne_eq, ← String.ofList_eq_empty_iff, ← startPos_eq_endPos_iff]
  refine ⟨ofList m.tail, ?_⟩
  rw (occs := [1]) [← List.cons_head_tail hm]
  rw [← List.singleton_append, String.ofList_append, append_left_inj, ← singleton_eq_ofList,
    get_startPos]
  simp

theorem Slice.copy_eq_copy_sliceTo {s : Slice} {pos : s.Pos} :
    s.copy = (s.sliceTo pos).copy ++ (s.sliceFrom pos).copy := by
  rw [← String.toByteArray_inj, toByteArray_copy, toByteArray_append, toByteArray_copy, toByteArray_copy]
  simp only [str_sliceTo, startInclusive_sliceTo, endExclusive_sliceTo, Pos.offset_str,
    Pos.Raw.byteIdx_offsetBy, str_sliceFrom, startInclusive_sliceFrom,
    endExclusive_sliceFrom, ByteArray.extract_append_extract, Nat.le_add_right, Nat.min_eq_left]
  rw [Nat.max_eq_right]
  exact pos.offset_str_le_offset_endExclusive

@[simp]
theorem Slice.sliceTo_append_sliceFrom {s : Slice} {pos : s.Pos} :
    (s.sliceTo pos).copy ++ (s.sliceFrom pos).copy = s.copy :=
  copy_eq_copy_sliceTo.symm

/-- Given a slice `s` and a position on `s.copy`, obtain the corresponding position on `s`. -/
@[inline]
def Pos.ofCopy {s : Slice} (pos : s.copy.Pos) : s.Pos where
  offset := pos.offset
  isValidForSlice := Pos.Raw.isValid_copy_iff.1 pos.isValid

@[simp]
theorem Pos.offset_ofCopy {s : Slice} {pos : s.copy.Pos} : pos.ofCopy.offset = pos.offset := (rfl)

/-- Given a slice `s` and a position on `s`, obtain the corresponding position on `s.copy.` -/
@[inline]
def Slice.Pos.copy {s : Slice} (pos : s.Pos) : s.copy.Pos where
  offset := pos.offset
  isValid := Pos.Raw.isValid_copy_iff.2 pos.isValidForSlice

@[deprecated Slice.Pos.copy (since := "2025-12-01")]
def Slice.Pos.toCopy {s : Slice} (pos : s.Pos) : s.copy.Pos :=
  pos.copy

@[simp]
theorem Slice.Pos.offset_copy {s : Slice} {pos : s.Pos} : pos.copy.offset = pos.offset := (rfl)

@[simp]
theorem Slice.Pos.ofCopy_copy {s : Slice} {pos : s.Pos} : pos.copy.ofCopy = pos :=
  Slice.Pos.ext (by simp)

@[simp]
theorem Pos.copy_ofCopy {s : Slice} {pos : s.copy.Pos} : pos.ofCopy.copy = pos :=
  Pos.ext (by simp)

theorem Pos.ofCopy_inj {s : Slice} {pos pos' : s.copy.Pos} : pos.ofCopy = pos'.ofCopy ↔ pos = pos' :=
  ⟨fun h => by simpa using congrArg Slice.Pos.copy h, (· ▸ rfl)⟩

@[simp]
theorem Slice.startPos_copy {s : Slice} : s.copy.startPos = s.startPos.copy :=
  String.Pos.ext (by simp)

@[simp]
theorem Slice.endPos_copy {s : Slice} : s.copy.endPos = s.endPos.copy :=
  String.Pos.ext (by simp)

theorem Slice.Pos.get_copy {s : Slice} {pos : s.Pos} (h) :
    pos.copy.get h = pos.get (by rintro rfl; simp at h) := by
  rw [String.Pos.get, Slice.Pos.get_eq_utf8DecodeChar, Slice.Pos.get_eq_utf8DecodeChar]
  simp only [str_toSlice, toByteArray_copy, startInclusive_toSlice, startPos_copy, offset_copy,
    Slice.offset_startPos, Pos.Raw.byteIdx_zero, Pos.offset_toSlice, Nat.zero_add]
  rw [ByteArray.utf8DecodeChar_eq_utf8DecodeChar_extract]
  conv => lhs; congr; rw [ByteArray.extract_extract]
  conv => rhs; rw [ByteArray.utf8DecodeChar_eq_utf8DecodeChar_extract]
  exact ByteArray.utf8DecodeChar_extract_congr _ _ _

theorem Slice.Pos.get_eq_get_copy {s : Slice} {pos : s.Pos} {h} :
    pos.get h = pos.copy.get (ne_of_apply_ne Pos.ofCopy (by simp [h])) :=
  (get_copy _).symm

theorem Slice.Pos.byte_copy {s : Slice} {pos : s.Pos} (h) :
    pos.copy.byte h = pos.byte (by rintro rfl; simp at h) := by
  rw [String.Pos.byte, Slice.Pos.byte, Slice.Pos.byte]
  simp [getUTF8Byte, String.getUTF8Byte, toByteArray_copy, ByteArray.getElem_extract]

theorem Slice.Pos.byte_eq_byte_copy {s : Slice} {pos : s.Pos} {h} :
    pos.byte h = pos.copy.byte (ne_of_apply_ne Pos.ofCopy (by simp [h])) :=
  (byte_copy _).symm

/-- Given a position in `s.sliceFrom p₀`, obtain the corresponding position in `s`. -/
@[inline, expose]
def Slice.Pos.ofSliceFrom {s : Slice} {p₀ : s.Pos} (pos : (s.sliceFrom p₀).Pos) : s.Pos where
  offset := pos.offset.offsetBy p₀.offset
  isValidForSlice := Pos.Raw.isValidForSlice_sliceFrom.1 pos.isValidForSlice

@[deprecated Slice.Pos.ofSliceFrom (since := "2025-11-20")]
def Slice.Pos.ofReplaceStart {s : Slice} {p₀ : s.Pos} (pos : (s.sliceFrom p₀).Pos) : s.Pos :=
  ofSliceFrom pos

@[simp]
theorem Slice.Pos.offset_ofSliceFrom {s : Slice} {p₀ : s.Pos} {pos : (s.sliceFrom p₀).Pos} :
    (ofSliceFrom pos).offset = pos.offset.offsetBy p₀.offset := (rfl)

/-- Given a position in `s` that is at least `p₀`, obtain the corresponding position in
`s.sliceFrom p₀`. -/
@[inline]
def Slice.Pos.sliceFrom {s : Slice} (p₀ : s.Pos) (pos : s.Pos) (h : p₀ ≤ pos) :
    (s.sliceFrom p₀).Pos where
  offset := pos.offset.unoffsetBy p₀.offset
  isValidForSlice := Pos.Raw.isValidForSlice_sliceFrom.2 (by
    simpa [Pos.Raw.offsetBy_unoffsetBy_of_le (Pos.Raw.le_iff.1 h)] using pos.isValidForSlice)

@[deprecated Slice.Pos.sliceFrom (since := "2025-11-20")]
def Slice.Pos.toReplaceStart {s : Slice} (p₀ : s.Pos) (pos : s.Pos) (h : p₀ ≤ pos) :
    (s.sliceFrom p₀).Pos :=
  sliceFrom p₀ pos h

@[simp]
theorem Slice.Pos.offset_sliceFrom {s : Slice} {p₀ : s.Pos} {pos : s.Pos} {h} :
    (sliceFrom p₀ pos h).offset = pos.offset.unoffsetBy p₀.offset := (rfl)

@[simp]
theorem Slice.Pos.sliceFrom_inj {s : Slice} {p₀ : s.Pos} {pos pos' : s.Pos} {h h'} :
    p₀.sliceFrom pos h = p₀.sliceFrom pos' h' ↔ pos = pos' := by
  simp [Pos.ext_iff, Pos.Raw.ext_iff, Pos.le_iff, Pos.Raw.le_iff] at ⊢ h h'
  omega

@[simp]
theorem Slice.Pos.ofSliceFrom_startPos {s : Slice} {pos : s.Pos} :
    ofSliceFrom (s.sliceFrom pos).startPos = pos :=
  Slice.Pos.ext (by simp)

@[simp]
theorem Slice.Pos.ofSliceFrom_endPos {s : Slice} {pos : s.Pos} :
    ofSliceFrom (s.sliceFrom pos).endPos = s.endPos := by
  have := pos.isValidForSlice.le_rawEndPos
  simp_all [Pos.ext_iff, String.Pos.Raw.ext_iff, Pos.Raw.le_iff]

theorem Slice.Pos.ofSliceFrom_inj {s : Slice} {p₀ : s.Pos} {pos pos' : (s.sliceFrom p₀).Pos} :
    ofSliceFrom pos = ofSliceFrom pos' ↔ pos = pos' := by
  simp [Pos.ext_iff, String.Pos.Raw.ext_iff]

theorem Slice.Pos.get_eq_get_ofSliceFrom {s : Slice} {p₀ : s.Pos} {pos : (s.sliceFrom p₀).Pos} {h} :
    pos.get h = (ofSliceFrom pos).get (by rwa [← ofSliceFrom_endPos, ne_eq, ofSliceFrom_inj]) := by
  simp [Slice.Pos.get, Nat.add_assoc]

/-- Given a position in `s.sliceTo p₀`, obtain the corresponding position in `s`. -/
@[inline]
def Slice.Pos.ofSliceTo {s : Slice} {p₀ : s.Pos} (pos : (s.sliceTo p₀).Pos) : s.Pos where
  offset := pos.offset
  isValidForSlice := (Pos.Raw.isValidForSlice_sliceTo.1 pos.isValidForSlice).2

@[deprecated Slice.Pos.ofSliceTo (since := "2025-11-20")]
def Slice.Pos.ofReplaceEnd {s : Slice} {p₀ : s.Pos} (pos : (s.sliceTo p₀).Pos) : s.Pos :=
  ofSliceTo pos

@[simp]
theorem Slice.Pos.offset_ofSliceTo {s : Slice} {p₀ : s.Pos} {pos : (s.sliceTo p₀).Pos} :
    (ofSliceTo pos).offset = pos.offset := (rfl)

/-- Given a position in `s` that is at most `p₀`, obtain the corresponding position in `s.sliceTo p₀`. -/
@[inline]
def Slice.Pos.sliceTo {s : Slice} (p₀ : s.Pos) (pos : s.Pos) (h : pos ≤ p₀) :
    (s.sliceTo p₀).Pos where
  offset := pos.offset
  isValidForSlice := Pos.Raw.isValidForSlice_sliceTo.2 ⟨h, pos.isValidForSlice⟩

@[deprecated Slice.Pos.sliceTo (since := "2025-11-20")]
def Slice.Pos.toReplaceEnd {s : Slice} (p₀ : s.Pos) (pos : s.Pos) (h : pos ≤ p₀) :
    (s.sliceTo p₀).Pos :=
  sliceTo p₀ pos h

@[simp]
theorem Slice.Pos.offset_sliceTo {s : Slice} {p₀ : s.Pos} {pos : s.Pos} {h : pos ≤ p₀} :
    (sliceTo p₀ pos h).offset = pos.offset := (rfl)

@[simp]
theorem Slice.Pos.sliceTo_inj {s : Slice} {p₀ : s.Pos} {pos pos' : s.Pos} {h h'} :
    p₀.sliceTo pos h = p₀.sliceTo pos' h' ↔ pos = pos' := by
  simp [Pos.ext_iff]

@[simp]
theorem Slice.Pos.ofSliceTo_startPos {s : Slice} {pos : s.Pos} :
    ofSliceTo (s.sliceTo pos).startPos = s.startPos := by
  simp [Pos.ext_iff]

@[simp]
theorem Slice.Pos.ofSliceTo_endPos {s : Slice} {pos : s.Pos} :
    ofSliceTo (s.sliceTo pos).endPos = pos := by
  simp [Pos.ext_iff]

theorem Slice.Pos.ofSliceTo_inj {s : Slice} {p₀ : s.Pos} {pos pos' : (s.sliceTo p₀).Pos} :
    ofSliceTo pos = ofSliceTo pos' ↔ pos = pos' := by
  simp [Pos.ext_iff]

theorem Slice.Pos.copy_eq_append_get {s : Slice} {pos : s.Pos} (h : pos ≠ s.endPos) :
    ∃ t₁ t₂ : String, s.copy = t₁ ++ singleton (pos.get h) ++ t₂ ∧ t₁.utf8ByteSize = pos.offset.byteIdx := by
  obtain ⟨t₂, ht₂⟩ := (s.sliceFrom pos).copy.eq_singleton_append (by simpa [← Pos.ofCopy_inj, ← ofSliceFrom_inj])
  refine ⟨(s.sliceTo pos).copy, t₂, ?_, by simp⟩
  simp only [Slice.startPos_copy, get_copy, get_eq_get_ofSliceFrom, ofSliceFrom_startPos] at ht₂
  rw [append_assoc, ← ht₂, ← copy_eq_copy_sliceTo]

theorem Slice.Pos.utf8ByteSize_byte {s : Slice} {pos : s.Pos} {h : pos ≠ s.endPos} :
    (pos.byte h).utf8ByteSize pos.isUTF8FirstByte_byte = (pos.get h).utf8Size := by
  simp [getUTF8Byte, byte, String.getUTF8Byte, get_eq_utf8DecodeChar, ByteArray.utf8Size_utf8DecodeChar]

theorem Pos.utf8ByteSize_byte {s : String} {pos : s.Pos} {h : pos ≠ s.endPos} :
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

theorem Slice.Pos.copy_eq_copy_sliceTo_append_get {s : Slice} {pos : s.Pos} (h : pos ≠ s.endPos) :
    s.copy = (s.sliceTo pos).copy ++ singleton (pos.get h) ++ (s.sliceFrom (pos.next h)).copy := by
  suffices (max (s.startInclusive.offset.byteIdx + (pos.offset.byteIdx + (pos.get h).utf8Size)) s.endExclusive.offset.byteIdx)
      = s.endExclusive.offset.byteIdx by
    simp [← toByteArray_inj, toByteArray_copy, utf8Encode_get_eq_extract, Nat.add_assoc, this]
  rw [Nat.max_eq_right]
  simpa [Pos.Raw.le_iff] using (pos.next h).offset_str_le_offset_endExclusive

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
@[expose, extern "lean_string_utf8_next_fast", tagged_return]
def Pos.next {s : @& String} (pos : @& s.Pos) (h : pos ≠ s.endPos) : s.Pos :=
  ofToSlice (Slice.Pos.next pos.toSlice (ne_of_apply_ne Pos.ofToSlice (by simpa)))

@[simp]
theorem Pos.ofToSlice_next_toSlice {s : String} {pos : s.Pos} {h} :
    ofToSlice (Slice.Pos.next pos.toSlice h) = pos.next (ne_of_apply_ne Pos.toSlice (by simpa using h)) :=
  rfl

@[simp]
theorem Slice.Pos.str_inj {s : Slice} (p₁ p₂ : s.Pos) : p₁.str = p₂.str ↔ p₁ = p₂ := by
  simp [Slice.Pos.ext_iff, String.Pos.ext_iff, Pos.Raw.ext_iff]

/-- Advances a valid position on a string to the next valid position, or returns `none` if the
given position is the past-the-end position. -/
@[inline, expose]
def Pos.next? {s : String} (pos : s.Pos) : Option s.Pos :=
  pos.toSlice.next?.map Pos.ofToSlice

/-- Advances a valid position on a string to the next valid position, or panics if the given
position is the past-the-end position. -/
@[inline, expose]
def Pos.next! {s : String} (pos : s.Pos) : s.Pos :=
  ofToSlice pos.toSlice.next!

/-- Constructs a valid position on `s` from a position and a proof that it is valid. -/
@[inline, expose]
def pos (s : String) (off : Pos.Raw) (h : off.IsValid s) : s.Pos :=
  Pos.ofToSlice (s.toSlice.pos off h.toSlice)

/-- Constructs a valid position on `s` from a position, returning `none` if the position is not valid. -/
@[inline, expose]
def pos? (s : String) (off : Pos.Raw) : Option s.Pos :=
  (s.toSlice.pos? off).map Pos.ofToSlice

/-- Constructs a valid position `s` from a position, panicking if the position is not valid. -/
@[inline, expose]
def pos! (s : String) (off : Pos.Raw) : s.Pos :=
  Pos.ofToSlice (s.toSlice.pos! off)

@[simp]
theorem offset_pos {s : String} {off : Pos.Raw} {h} : (s.pos off h).offset = off := rfl

/-- Constructs a valid position on `t` from a valid position on `s` and a proof that
`s.copy = t.copy`. -/
@[inline]
def Slice.Pos.cast {s t : Slice} (pos : s.Pos) (h : s.copy = t.copy) : t.Pos where
  offset := pos.offset
  isValidForSlice := Pos.Raw.isValid_copy_iff.mp (h ▸ Pos.Raw.isValid_copy_iff.mpr pos.isValidForSlice)

@[simp]
theorem Slice.Pos.offset_cast {s t : Slice} {pos : s.Pos} {h : s.copy = t.copy} :
    (pos.cast h).offset = pos.offset := (rfl)

@[simp]
theorem Slice.Pos.cast_rfl {s : Slice} {pos : s.Pos} : pos.cast rfl = pos :=
  Slice.Pos.ext (by simp)

@[simp]
theorem Slice.Pos.cast_cast {s t u : Slice} {hst : s.copy = t.copy} {htu : t.copy = u.copy}
    {pos : s.Pos} : (pos.cast hst).cast htu = pos.cast (hst.trans htu) :=
  Slice.Pos.ext (by simp)

@[simp]
theorem Slice.Pos.cast_inj {s t : Slice} {hst : s.copy = t.copy} {p q : s.Pos} : p.cast hst = q.cast hst ↔ p = q := by
  simp [Slice.Pos.ext_iff]

@[simp]
theorem Slice.Pos.cast_startPos {s t : Slice} {hst : s.copy = t.copy} : s.startPos.cast hst = t.startPos :=
  Slice.Pos.ext (by simp)

@[simp]
theorem Slice.Pos.cast_eq_startPos {s t : Slice} {p : s.Pos} {hst : s.copy = t.copy} : p.cast hst = t.startPos ↔ p = s.startPos := by
  rw [← cast_startPos (hst := hst), Pos.cast_inj]

@[simp]
theorem Slice.Pos.cast_endPos {s t : Slice} {hst : s.copy = t.copy} : s.endPos.cast hst = t.endPos :=
  Slice.Pos.ext (by simp [← rawEndPos_copy, hst])

@[simp]
theorem Slice.Pos.cast_eq_endPos {s t : Slice} {p : s.Pos} {hst : s.copy = t.copy} : p.cast hst = t.endPos ↔ p = s.endPos := by
  rw [← cast_endPos (hst := hst), Pos.cast_inj]

@[simp]
theorem Slice.Pos.cast_le_cast_iff {s t : Slice} {pos pos' : s.Pos} {h : s.copy = t.copy} :
    pos.cast h ≤ pos'.cast h ↔ pos ≤ pos' := by
  simp [Slice.Pos.le_iff]

@[simp]
theorem Slice.Pos.cast_lt_cast_iff {s t : Slice} {pos pos' : s.Pos} {h : s.copy = t.copy} :
    pos.cast h < pos'.cast h ↔ pos < pos' := by
  simp [Slice.Pos.lt_iff]

theorem Slice.Pos.cast_le_iff {s t : Slice} {pos : s.Pos} {pos' : t.Pos} {h : s.copy = t.copy} :
    pos.cast h ≤ pos' ↔ pos ≤ pos'.cast h.symm := by
  simp [Slice.Pos.le_iff]

theorem Slice.Pos.le_cast_iff {s t : Slice} {pos : t.Pos} {pos' : s.Pos} {h : s.copy = t.copy} :
    pos ≤ pos'.cast h ↔ pos.cast h.symm ≤ pos' := by
  simp [Slice.Pos.le_iff]

theorem Slice.Pos.cast_lt_iff {s t : Slice} {pos : s.Pos} {pos' : t.Pos} {h : s.copy = t.copy} :
    pos.cast h < pos' ↔ pos < pos'.cast h.symm := by
  simp [Slice.Pos.lt_iff]

theorem Slice.Pos.lt_cast_iff {s t : Slice} {pos : t.Pos} {pos' : s.Pos} {h : s.copy = t.copy} :
    pos < pos'.cast h ↔ pos.cast h.symm < pos' := by
  simp [Slice.Pos.lt_iff]

/-- Constructs a valid position on `t` from a valid position on `s` and a proof that `s = t`. -/
@[inline]
def Pos.cast {s t : String} (pos : s.Pos) (h : s = t) : t.Pos where
  offset := pos.offset
  isValid := h ▸ pos.isValid

@[simp]
theorem Pos.offset_cast {s t : String} {pos : s.Pos} {h : s = t} :
    (pos.cast h).offset = pos.offset := (rfl)

@[simp]
theorem Pos.cast_rfl {s : String} {pos : s.Pos} : pos.cast rfl = pos :=
  Pos.ext (by simp)

@[simp]
theorem Pos.cast_cast {s t u : String} {hst : s = t} {htu : t = u}
    {pos : s.Pos} : (pos.cast hst).cast htu = pos.cast (hst.trans htu) :=
  Pos.ext (by simp)

@[simp]
theorem Pos.cast_inj {s t : String} {hst : s = t} {p q : s.Pos} : p.cast hst = q.cast hst ↔ p = q := by
  simp [Pos.ext_iff]

@[simp]
theorem Pos.cast_startPos {s t : String} {hst : s = t} : s.startPos.cast hst = t.startPos := by
  subst hst; simp

@[simp]
theorem Pos.cast_eq_startPos {s t : String} {hst : s = t} {p : s.Pos} : p.cast hst = t.startPos ↔ p = s.startPos := by
  rw [← Pos.cast_startPos (hst := hst), Pos.cast_inj]

@[simp]
theorem Pos.cast_endPos {s t : String} {hst : s = t} : s.endPos.cast hst = t.endPos := by
  subst hst; simp

@[simp]
theorem Pos.cast_eq_endPos {s t : String} {hst : s = t} {p : s.Pos} : p.cast hst = t.endPos ↔ p = s.endPos := by
  rw [← Pos.cast_endPos (hst := hst), Pos.cast_inj]

@[simp]
theorem Pos.cast_le_cast_iff {s t : String} {pos pos' : s.Pos} {h : s = t} :
    pos.cast h ≤ pos'.cast h ↔ pos ≤ pos' := by
  cases h; simp

@[simp]
theorem Pos.cast_lt_cast_iff {s t : String} {pos pos' : s.Pos} {h : s = t} :
    pos.cast h < pos'.cast h ↔ pos < pos' := by
  cases h; simp

theorem Pos.cast_le_iff {s t : String} {pos : s.Pos} {pos' : t.Pos} {h : s = t} :
    pos.cast h ≤ pos' ↔ pos ≤ pos'.cast h.symm := by
  simp [Pos.le_iff]

theorem Pos.le_cast_iff {s t : String} {pos : t.Pos} {pos' : s.Pos} {h : s = t} :
    pos ≤ pos'.cast h ↔ pos.cast h.symm ≤ pos' := by
  simp [Pos.le_iff]

theorem Pos.cast_lt_iff {s t : String} {pos : s.Pos} {pos' : t.Pos} {h : s = t} :
    pos.cast h < pos' ↔ pos < pos'.cast h.symm := by
  simp [Pos.lt_iff]

theorem Pos.lt_cast_iff {s t : String} {pos : t.Pos} {pos' : s.Pos} {h : s = t} :
    pos < pos'.cast h ↔ pos.cast h.symm < pos' := by
  simp [Pos.lt_iff]

theorem Pos.copy_toSlice_eq_cast {s : String} (p : s.Pos) :
    p.toSlice.copy = p.cast copy_toSlice.symm :=
  Pos.ext (by simp)

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

This is a legacy function. The recommended alternative is `String.Pos.get`, combined with
`String.pos` or another means of obtaining a `String.Pos`.

Examples:
* `"abc".get ⟨1⟩ = 'b'`
* `"abc".get ⟨3⟩ = (default : Char)` because byte `3` is at the end of the string.
* `"L∃∀N".get ⟨2⟩ = (default : Char)` because byte `2` is in the middle of `'∃'`.
-/
@[extern "lean_string_utf8_get", expose]
def Pos.Raw.get (s : @& String) (p : @& Pos.Raw) : Char :=
  utf8GetAux s.toList 0 p

@[extern "lean_string_utf8_get", expose, deprecated Pos.Raw.get (since := "2025-10-14")]
def get (s : @& String) (p : @& Pos.Raw) : Char :=
  Pos.Raw.utf8GetAux s.toList 0 p

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

This is a legacy function. The recommended alternative is `String.Pos.get`, combined with
`String.pos?` or another means of obtaining a `String.Pos`.

Examples:
* `"abc".get? ⟨1⟩ = some 'b'`
* `"abc".get? ⟨3⟩ = none`
* `"L∃∀N".get? ⟨1⟩ = some '∃'`
* `"L∃∀N".get? ⟨2⟩ = none`
-/
@[extern "lean_string_utf8_get_opt", expose]
def Pos.Raw.get? : (@& String) → (@& Pos.Raw) → Option Char
  | s, p => utf8GetAux? s.toList 0 p

@[extern "lean_string_utf8_get_opt", expose, deprecated Pos.Raw.get? (since := "2025-10-14")]
def get? : (@& String) → (@& Pos.Raw) → Option Char
  | s, p => Pos.Raw.utf8GetAux? s.toList 0 p

/--
Returns the character at position `p` of a string. Panics if `p` is not a valid position.

See `String.pos?` and `String.Pos.get` for a safer alternative.

This function is overridden with an efficient implementation in runtime code. See
`String.utf8GetAux` for the reference implementation.

This is a legacy function. The recommended alternative is `String.Pos.get`, combined with
`String.pos!` or another means of obtaining a `String.Pos`.

Examples
* `"abc".get! ⟨1⟩ = 'b'`
-/
@[extern "lean_string_utf8_get_bang", expose]
def Pos.Raw.get! (s : @& String) (p : @& Pos.Raw) : Char :=
  match s with
  | s => Pos.Raw.utf8GetAux s.toList 0 p

@[extern "lean_string_utf8_get_bang", expose, deprecated Pos.Raw.get! (since := "2025-10-14")]
def get! (s : @& String) (p : @& Pos.Raw) : Char :=
  match s with
  | s => Pos.Raw.utf8GetAux s.toList 0 p

@[expose]
def Pos.Raw.utf8SetAux (c' : Char) : List Char → Pos.Raw → Pos.Raw → List Char
  | [],    _, _ => []
  | c::cs, i, p =>
    if i = p then (c'::cs) else c::(utf8SetAux c' cs (i + c) p)

@[deprecated Pos.Raw.utf8SetAux (since := "2025-10-09")]
abbrev utf8SetAux (c' : Char) : List Char → Pos.Raw → Pos.Raw → List Char :=
  Pos.Raw.utf8SetAux c'

@[simp]
theorem Pos.get_toSlice {s : String} {p : s.Pos} {h} :
    p.toSlice.get h = p.get (ne_of_apply_ne (·.toSlice) (by simp_all)) := by
  rfl

theorem Pos.get_eq_get_toSlice {s : String} {p : s.Pos} {h}  :
    p.get h = p.toSlice.get (ne_of_apply_ne Pos.ofToSlice (by simp [h])) := rfl

@[simp]
theorem Pos.offset_next {s : String} (p : s.Pos) (h : p ≠ s.endPos) :
    (p.next h).offset = p.offset + p.get h := by
  simp [next, -ofToSlice_next_toSlice]

theorem Pos.byteIdx_offset_next {s : String} (p : s.Pos) (h : p ≠ s.endPos) :
    (p.next h).offset.byteIdx = p.offset.byteIdx + (p.get h).utf8Size := by
  simp

theorem Pos.toSlice_next {s : String} {p : s.Pos} {h} :
    (p.next h).toSlice = p.toSlice.next (ne_of_apply_ne Pos.ofToSlice (by simpa)) := by
  simp [next, -ofToSlice_next_toSlice]

theorem Pos.next_toSlice {s : String} {p : s.Pos} {h} :
    p.toSlice.next h = (p.next (ne_of_apply_ne Pos.toSlice (by simpa using h))).toSlice := by
  simp [Pos.toSlice_next]

theorem Pos.byteIdx_lt_utf8ByteSize {s : String} (p : s.Pos) (h : p ≠ s.endPos) :
    p.offset.byteIdx < s.utf8ByteSize := by
  have := byteIdx_rawEndPos ▸ Pos.Raw.le_iff.1 p.isValid.le_rawEndPos
  simp only [ne_eq, Pos.ext_iff, offset_endPos, Pos.Raw.ext_iff, byteIdx_rawEndPos] at h
  omega

@[simp]
theorem Pos.lt_next {s : String} {p : s.Pos} {h} : p < p.next h := by
  simp [← Pos.toSlice_lt, toSlice_next]

theorem Pos.ne_startPos_of_lt {s : String} {p q : s.Pos} :
    p < q → q ≠ s.startPos := by
  simp only [lt_iff, Pos.Raw.lt_iff, ne_eq, Pos.ext_iff, offset_startPos, Pos.Raw.ext_iff,
    Pos.Raw.byteIdx_zero]
  omega

@[simp]
theorem Pos.next_ne_startPos {s : String} {p : s.Pos} {h} :
    p.next h ≠ s.startPos :=
  ne_startPos_of_lt p.lt_next

@[simp]
theorem Pos.str_toSlice {s : String} {p : s.Pos} : p.toSlice.str = p := by
  ext
  simp

theorem Slice.Pos.str_le_endExclusive {s : Slice} (p : s.Pos) :
    p.str ≤ s.endExclusive := by
  have := p.isValidForSlice.le_utf8ByteSize
  have := s.startInclusive_le_endExclusive
  simp [String.Pos.le_iff, Pos.Raw.le_iff, Slice.utf8ByteSize_eq] at *
  omega

theorem Pos.lt_of_le_of_ne {s : String} {p q : s.Pos} :
    p ≤ q → p ≠ q → p < q := by
  simp [Pos.le_iff, Pos.lt_iff, Pos.ext_iff, Pos.Raw.le_iff, Pos.Raw.lt_iff,
    Pos.Raw.ext_iff]
  omega

@[simp]
theorem Slice.Pos.str_endPos {s : Slice} : s.endPos.str = s.endExclusive := by
  simp [String.Pos.ext_iff]

theorem Slice.Pos.str_lt_endExclusive {s : Slice} (p : s.Pos) (h : p ≠ s.endPos) :
    p.str < s.endExclusive :=
  Pos.lt_of_le_of_ne p.str_le_endExclusive (by rwa [← str_endPos, ne_eq, str_inj])

theorem Pos.ne_of_lt {s : String} {p q : s.Pos} : p < q → p ≠ q := by
  simpa [Pos.lt_iff, Pos.ext_iff] using Pos.Raw.ne_of_lt

theorem Pos.lt_of_lt_of_le {s : String} {p q r : s.Pos} : p < q → q ≤ r → p < r := by
  simpa [Pos.lt_iff, Pos.le_iff] using Pos.Raw.lt_of_lt_of_le

@[simp]
theorem Pos.le_endPos {s : String} (p : s.Pos) : p ≤ s.endPos := by
  simpa [Pos.le_iff] using p.isValid.le_rawEndPos

@[simp]
theorem Slice.Pos.le_endPos {s : Slice} (p : s.Pos) : p ≤ s.endPos :=
  p.isValidForSlice.le_rawEndPos

theorem Slice.Pos.str_ne_endPos {s : Slice} (p : s.Pos) (h : p ≠ s.endPos) :
    p.str ≠ s.str.endPos :=
  Pos.ne_of_lt (Pos.lt_of_lt_of_le (p.str_lt_endExclusive h) (String.Pos.le_endPos _))

theorem Pos.le_trans {s : String} {p q r : s.Pos} : p ≤ q → q ≤ r → p ≤ r := by
  simpa [Pos.le_iff] using Pos.Raw.le_trans

theorem Pos.le_of_lt {s : String} {p q : s.Pos} : p < q → p ≤ q := by
  simpa [Pos.le_iff, Pos.lt_iff] using Pos.Raw.le_of_lt

theorem Slice.Pos.le_of_not_lt {s : Slice} {p q : s.Pos} : ¬q < p → p ≤ q := by
  simp [Slice.Pos.le_iff, Slice.Pos.lt_iff, Pos.Raw.le_iff, Pos.Raw.lt_iff]

theorem Slice.Pos.ne_endPos_of_lt {s : Slice} {p q : s.Pos} : p < q → p ≠ s.endPos := by
  have := q.isValidForSlice.le_utf8ByteSize
  simp [lt_iff, Pos.ext_iff, Pos.Raw.lt_iff, Pos.Raw.ext_iff]
  omega

theorem Slice.Pos.next_le_of_lt {s : Slice} {p q : s.Pos} {h} : p < q → p.next h ≤ q := by
  -- Things like this will become a lot simpler once we have the `Splits` machinery developed,
  -- but this is `String.Basic`, so we have to suffer a little.
  refine fun hpq => le_of_not_lt (fun hq => ?_)
  have := q.isUTF8FirstByte_byte (h := ne_endPos_of_lt hq)
  rw [byte, getUTF8Byte, String.getUTF8Byte] at this
  simp only [Pos.Raw.byteIdx_offsetBy] at this
  have h₁ : q.offset.byteIdx = p.offset.byteIdx + (q.offset.byteIdx - p.offset.byteIdx) := by
    simp [lt_iff, Pos.Raw.lt_iff] at hpq
    omega
  have h₂ : q.offset.byteIdx - p.offset.byteIdx < (p.get h).utf8Size := by
    simp [lt_iff, Pos.Raw.lt_iff] at hq
    omega
  conv at this => congr; arg 2; rw [h₁, ← Nat.add_assoc]
  rw [← ByteArray.getElem_extract (start := s.startInclusive.offset.byteIdx + p.offset.byteIdx)
    (stop := s.startInclusive.offset.byteIdx + p.offset.byteIdx + (p.get h).utf8Size)] at this
  · simp only [← utf8Encode_get_eq_extract, List.utf8Encode_singleton] at this
    have h₃ := List.getElem_toByteArray (l := utf8EncodeChar (p.get h))
      (i := q.offset.byteIdx - p.offset.byteIdx) (h := by simpa)
    rw [h₃, UInt8.isUTF8FirstByte_getElem_utf8EncodeChar] at this
    simp only [lt_iff, Pos.Raw.lt_iff] at hpq
    omega
  · simp only [ByteArray.size_extract, size_toByteArray]
    rw [Nat.min_eq_left]
    · omega
    · have := (p.next h).str.isValid.le_utf8ByteSize
      simpa [Nat.add_assoc] using this

theorem Pos.ofToSlice_le_iff {s : String} {p : s.toSlice.Pos} {q : s.Pos} :
    ofToSlice p ≤ q ↔ p ≤ q.toSlice := Iff.rfl

theorem Pos.ofToSlice_lt_iff {s : String} {p : s.toSlice.Pos} {q : s.Pos} :
    ofToSlice p < q ↔ p < q.toSlice := Iff.rfl

theorem Pos.lt_ofToSlice_iff {s : String} {p : s.Pos} {q : s.toSlice.Pos} :
    p < ofToSlice q ↔ p.toSlice < q := Iff.rfl

theorem Pos.le_ofToSlice_iff {s : String} {p : s.Pos} {q : s.toSlice.Pos} :
    p ≤ ofToSlice q ↔ p.toSlice ≤ q := Iff.rfl

@[simp]
theorem Pos.toSlice_lt_toSlice_iff {s : String} {p q : s.Pos} :
    p.toSlice < q.toSlice ↔ p < q := Iff.rfl

@[simp]
theorem Pos.toSlice_le_toSlice_iff {s : String} {p q : s.Pos} :
    p.toSlice ≤ q.toSlice ↔ p ≤ q := Iff.rfl

theorem Pos.next_le_of_lt {s : String} {p q : s.Pos} {h} : p < q → p.next h ≤ q := by
  rw [next, Pos.ofToSlice_le_iff, ← Pos.toSlice_lt_toSlice_iff]
  exact Slice.Pos.next_le_of_lt

theorem Slice.Pos.get_eq_get_str {s : Slice} {p : s.Pos} {h} :
    p.get h = p.str.get (str_ne_endPos _ h) := by
  simp [String.Pos.get, Slice.Pos.get]

@[inline]
def Slice.Pos.nextFast {s : Slice} (pos : s.Pos) (h : pos ≠ s.endPos) : s.Pos :=
  ofStr (pos.str.next (str_ne_endPos _ h))
    (Pos.le_trans Slice.Pos.startInclusive_le_str (Pos.le_of_lt String.Pos.lt_next))
    (String.Pos.next_le_of_lt (Slice.Pos.str_lt_endExclusive _ h))

@[csimp]
theorem Slice.Pos.next_eq_nextFast : @Slice.Pos.next = @Slice.Pos.nextFast := by
  funext s pos h
  simp [Slice.Pos.ext_iff, Slice.Pos.nextFast, Pos.Raw.ext_iff, Slice.Pos.get_eq_get_str]
  omega

/-- The slice from the beginning of `s` up to `p` (exclusive). -/
@[inline, expose]
def sliceTo (s : String) (p : s.Pos) : Slice :=
  s.toSlice.sliceTo p.toSlice

@[deprecated sliceTo (since :="2025-11-20")]
def replaceEnd (s : String) (p : s.Pos) : Slice :=
  s.sliceTo p

@[simp]
theorem str_sliceTo {s : String} {p : s.Pos} : (s.sliceTo p).str = s := rfl

@[simp]
theorem startInclusive_sliceTo {s : String} {p : s.Pos} :
    (s.sliceTo p).startInclusive = s.startPos := by
  simp [sliceTo]

@[simp]
theorem endExclusive_sliceTo {s : String} {p : s.Pos} :
    (s.sliceTo p).endExclusive = p := by
  simp [sliceTo]

@[simp]
theorem rawEndPos_sliceTo {s : String} {p : s.Pos} :
    (s.sliceTo p).rawEndPos = p.offset := by
  simp [sliceTo]

theorem Pos.Raw.isValidForSlice_stringSliceTo {s : String} {p : s.Pos} {q : Pos.Raw} :
    q.IsValidForSlice (s.sliceTo p) ↔ q ≤ p.offset ∧ q.IsValid s := by
  rw [sliceTo, isValidForSlice_sliceTo, Pos.offset_toSlice, isValidForSlice_toSlice_iff]

/-- The slice from `p` (inclusive) up to the end of `s`. -/
@[inline, expose]
def sliceFrom (s : String) (p : s.Pos) : Slice :=
  s.toSlice.sliceFrom p.toSlice

@[deprecated sliceFrom (since := "2025-11-20")]
def replaceStart (s : String) (p : s.Pos) : Slice :=
  s.sliceFrom p

@[simp]
theorem str_sliceFrom {s : String} {p : s.Pos} : (s.sliceFrom p).str = s := rfl

@[simp]
theorem startInclusive_sliceFrom {s : String} {p : s.Pos} :
    (s.sliceFrom p).startInclusive = p := by
  simp [sliceFrom]

@[simp]
theorem endExclusive_sliceFrom {s : String} {p : s.Pos} :
    (s.sliceFrom p).endExclusive = s.endPos := by
  simp [sliceFrom]

@[simp]
theorem utf8ByteSize_toSlice {s : String} : s.toSlice.utf8ByteSize = s.utf8ByteSize := by
  simp [Slice.utf8ByteSize_eq]

@[simp]
theorem utf8ByteSize_sliceFrom {s : String} {p : s.Pos} :
    (s.sliceFrom p).utf8ByteSize = s.utf8ByteSize - p.offset.byteIdx := by
  simp [sliceFrom]

@[simp]
theorem utf8ByteSize_sliceTo {s : String} {p : s.Pos} :
    (s.sliceTo p).utf8ByteSize = p.offset.byteIdx := by
  simp [sliceTo]

theorem Pos.Raw.isValidForSlice_stringSliceFrom {s : String} {p : s.Pos} {q : Pos.Raw} :
    q.IsValidForSlice (s.sliceFrom p) ↔ (q.offsetBy p.offset).IsValid s := by
  rw [sliceFrom, isValidForSlice_sliceFrom, isValidForSlice_toSlice_iff,
    Pos.offset_toSlice]

@[simp]
theorem sliceFrom_toSlice {s : String} {p : s.Pos} :
    s.toSlice.sliceFrom p.toSlice = s.sliceFrom p := rfl

@[simp]
theorem sliceTo_toSlice {s : String} {p : s.Pos} :
    s.toSlice.sliceTo p.toSlice = s.sliceTo p := rfl

/--
Given a string and two valid positions within the string, obtain a slice on the string formed by
the two positions.

This happens to be equivalent to the constructor of `String.Slice`.
-/
@[inline, expose] -- For the defeq `(s.slice p₁ p₂).str = s`
def slice (s : String) (startInclusive endExclusive : s.Pos)
    (h : startInclusive ≤ endExclusive) : String.Slice :=
  s.toSlice.slice startInclusive.toSlice endExclusive.toSlice (by simpa)

@[simp]
theorem str_slice {s : String} {startInclusive endExclusive h} :
    (s.slice startInclusive endExclusive h).str = s := rfl

@[simp]
theorem startInclusive_slice {s : String} {startInclusive endExclusive h}  :
    (s.slice startInclusive endExclusive h).startInclusive = startInclusive := by
  simp [slice]

@[simp]
theorem endExclusive_slice {s : String} {startInclusive endExclusive h}  :
    (s.slice startInclusive endExclusive h).endExclusive = endExclusive := by
  simp [slice]

@[simp]
theorem utf8ByteSize_slice {s : String} {p₁ p₂ : s.Pos} {h} :
    (s.slice p₁ p₂ h).utf8ByteSize = p₂.offset.byteIdx - p₁.offset.byteIdx := by
  simp [Slice.utf8ByteSize_eq]

@[simp]
theorem slice_toSlice {s : String} {p₁ p₂ : s.Pos} {h} :
    s.toSlice.slice p₁.toSlice p₂.toSlice h = s.slice p₁ p₂ h := rfl

/-- Given a string and two valid positions within the string, obtain a slice on the string formed
by the new bounds, or return `none` if the given end is strictly less then the given start. -/
def slice? (s : String) (startInclusive endExclusive : s.Pos) :=
  if h : startInclusive ≤ endExclusive then
    some (s.slice startInclusive endExclusive h)
  else
    none

/--
Given a string and two valid positions within the string, obtain a slice on the string formed by
the new bounds, or panic if the given end is strictly less than the given start.
-/
def slice! (s : String) (p₁ p₂ : s.Pos) : Slice :=
  s.toSlice.slice! p₁.toSlice p₂.toSlice

@[deprecated slice! (since := "2025-11-20")]
def replaceStartEnd! (s : String) (p₁ p₂ : s.Pos) : Slice :=
  s.slice! p₁ p₂

theorem Pos.utf8Encode_get_eq_extract {s : String} (pos : s.Pos) (h : pos ≠ s.endPos) :
    List.utf8Encode [pos.get h] = s.toByteArray.extract pos.offset.byteIdx (pos.offset.byteIdx + (pos.get h).utf8Size) := by
  rw [get_eq_get_toSlice, Slice.Pos.utf8Encode_get_eq_extract]
  simp

theorem Pos.eq_copy_sliceTo_append_get {s : String} {pos : s.Pos} (h : pos ≠ s.endPos) :
    s = (s.sliceTo pos).copy ++ singleton (pos.get h) ++ (s.sliceFrom (pos.next h)).copy := by
  simp [← toByteArray_inj, utf8Encode_get_eq_extract pos h, Slice.toByteArray_copy, ← size_toByteArray]

/-- Given a position in `s.sliceFrom p₀`, obtain the corresponding position in `s`. -/
@[inline]
def Pos.ofSliceFrom {s : String} {p₀ : s.Pos} (pos : (s.sliceFrom p₀).Pos) :
    s.Pos where
  offset := pos.offset.offsetBy p₀.offset
  isValid := Pos.Raw.isValidForSlice_stringSliceFrom.1 pos.isValidForSlice

@[deprecated Pos.ofSliceFrom (since := "2025-11-20")]
def Pos.ofReplaceStart {s : String} {p₀ : s.Pos} (pos : (s.sliceFrom p₀).Pos) :
    s.Pos :=
  ofSliceFrom pos

@[simp]
theorem Pos.offset_ofSliceFrom {s : String} {p₀ : s.Pos}
    {pos : (s.sliceFrom p₀).Pos} : (ofSliceFrom pos).offset = pos.offset.offsetBy p₀.offset :=
  (rfl)

/-- Given a position in `s` that is at least `p₀`, obtain the corresponding position in
`s.sliceFrom p₀`. -/
@[inline]
def Pos.sliceFrom {s : String} (p₀ : s.Pos) (pos : s.Pos) (h : p₀ ≤ pos) :
    (s.sliceFrom p₀).Pos where
  offset := pos.offset.unoffsetBy p₀.offset
  isValidForSlice := Pos.Raw.isValidForSlice_stringSliceFrom.2 (by
    simpa [Pos.Raw.offsetBy_unoffsetBy_of_le (Pos.Raw.le_iff.1 h)] using pos.isValid)

@[deprecated Pos.sliceFrom (since := "2025-11-20")]
def Pos.toReplaceStart {s : String} (p₀ : s.Pos) (pos : s.Pos) (h : p₀ ≤ pos) :
    (s.sliceFrom p₀).Pos :=
  sliceFrom p₀ pos h

@[simp]
theorem Pos.offset_sliceFrom {s : String} {p₀ : s.Pos} {pos : s.Pos} {h} :
    (sliceFrom p₀ pos h).offset = pos.offset.unoffsetBy p₀.offset := (rfl)

@[simp]
theorem Pos.sliceFrom_inj {s : String} {p₀ : s.Pos} {pos pos' : s.Pos} {h h'} :
    p₀.sliceFrom pos h = p₀.sliceFrom pos' h' ↔ pos = pos' := by
  simp [Pos.ext_iff, Pos.Raw.ext_iff, Slice.Pos.ext_iff, Pos.le_iff, Pos.Raw.le_iff] at ⊢ h h'
  omega

@[simp]
theorem Pos.ofSliceFrom_startPos {s : String} {pos : s.Pos} :
    ofSliceFrom (s.sliceFrom pos).startPos = pos :=
  Pos.ext (by simp)

@[simp]
theorem Pos.ofSliceFrom_endPos {s : String} {pos : s.Pos} :
    ofSliceFrom (s.sliceFrom pos).endPos = s.endPos := by
  have := pos.isValid.le_rawEndPos
  simp_all [Pos.ext_iff, String.Pos.Raw.ext_iff, Pos.Raw.le_iff]

theorem Pos.ofSliceFrom_inj {s : String} {p₀ : s.Pos}
    {pos pos' : (s.sliceFrom p₀).Pos} :
    ofSliceFrom pos = ofSliceFrom pos' ↔ pos = pos' := by
  simp [Pos.ext_iff, String.Pos.Raw.ext_iff, Slice.Pos.ext_iff]

@[simp]
theorem Pos.le_ofSliceFrom {s : String} {p₀ : s.Pos} {pos : (s.sliceFrom p₀).Pos} :
    p₀ ≤ ofSliceFrom pos := by
  simp [Pos.le_iff, Pos.Raw.le_iff]

@[simp]
theorem Slice.Pos.le_ofSliceFrom {s : Slice} {p₀ : s.Pos} {pos : (s.sliceFrom p₀).Pos} :
    p₀ ≤ ofSliceFrom pos := by
  simp [Pos.le_iff, Pos.Raw.le_iff]

@[simp]
theorem Slice.Pos.ofSliceFrom_lt_ofSliceFrom_iff {s : Slice} {p : s.Pos}
    {q r : (s.sliceFrom p).Pos} : Slice.Pos.ofSliceFrom q < Slice.Pos.ofSliceFrom r ↔ q < r := by
  simp [Slice.Pos.lt_iff, Pos.Raw.lt_iff]

@[simp]
theorem Slice.Pos.ofSliceFrom_le_ofSliceFrom_iff {s : Slice} {p : s.Pos}
    {q r : (s.sliceFrom p).Pos} : Slice.Pos.ofSliceFrom q ≤ Slice.Pos.ofSliceFrom r ↔ q ≤ r := by
  simp [Slice.Pos.le_iff, Pos.Raw.le_iff]

@[simp]
theorem Pos.ofSliceFrom_lt_ofSliceFrom_iff {s : String} {p : s.Pos}
    {q r : (s.sliceFrom p).Pos} : Pos.ofSliceFrom q < Pos.ofSliceFrom r ↔ q < r := by
  simp [Pos.lt_iff, Slice.Pos.lt_iff, Pos.Raw.lt_iff]

@[simp]
theorem Pos.ofSliceFrom_le_ofSliceFrom_iff {s : String} {p : s.Pos}
    {q r : (s.sliceFrom p).Pos} : Pos.ofSliceFrom q ≤ Pos.ofSliceFrom r ↔ q ≤ r := by
  simp [Pos.le_iff, Slice.Pos.le_iff, Pos.Raw.le_iff]

theorem Pos.get_eq_get_ofSliceFrom {s : String} {p₀ : s.Pos}
    {pos : (s.sliceFrom p₀).Pos} {h} :
    pos.get h = (ofSliceFrom pos).get (by rwa [← ofSliceFrom_endPos, ne_eq, ofSliceFrom_inj]) := by
  simp [Pos.get, Slice.Pos.get]

@[simp]
theorem Slice.Pos.ofSliceFrom_sliceFrom {s : Slice} {p₀ p : s.Pos} {h : p₀ ≤ p} :
    Slice.Pos.ofSliceFrom (p₀.sliceFrom p h) = p := by
  simpa [Pos.ext_iff] using Pos.Raw.offsetBy_unoffsetBy_of_le h

@[simp]
theorem Slice.Pos.sliceFrom_ofSliceFrom {s : Slice} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos} :
    p₀.sliceFrom (Slice.Pos.ofSliceFrom p) Slice.Pos.le_ofSliceFrom = p := by
  simp [← Slice.Pos.ofSliceFrom_inj]

@[simp]
theorem Pos.ofSliceFrom_sliceFrom {s : String} {p₀ p : s.Pos} {h : p₀ ≤ p} :
    Pos.ofSliceFrom (p₀.sliceFrom p h) = p := by
  simpa [Pos.ext_iff] using Pos.Raw.offsetBy_unoffsetBy_of_le h

@[simp]
theorem Pos.sliceFrom_ofSliceFrom {s : String} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos} :
    p₀.sliceFrom (Pos.ofSliceFrom p) Pos.le_ofSliceFrom = p := by
  simp [← Pos.ofSliceFrom_inj]

/-- Given a position in `s.sliceTo p₀`, obtain the corresponding position in `s`. -/
@[inline]
def Pos.ofSliceTo {s : String} {p₀ : s.Pos} (pos : (s.sliceTo p₀).Pos) : s.Pos where
  offset := pos.offset
  isValid := (Pos.Raw.isValidForSlice_stringSliceTo.1 pos.isValidForSlice).2

@[deprecated Pos.ofSliceTo (since := "2025-11-20")]
def Pos.ofReplaceEnd {s : String} {p₀ : s.Pos} (pos : (s.sliceTo p₀).Pos) : s.Pos :=
  ofSliceTo pos

@[simp]
theorem Pos.offset_ofSliceTo {s : String} {p₀ : s.Pos} {pos : (s.sliceTo p₀).Pos} :
    (ofSliceTo pos).offset = pos.offset := (rfl)

@[simp]
theorem Pos.ofSliceTo_startPos {s : String} {pos : s.Pos} :
    ofSliceTo (s.sliceTo pos).startPos = s.startPos := by
  simp [Pos.ext_iff]

@[simp]
theorem Pos.ofSliceTo_endPos {s : String} {pos : s.Pos} :
    ofSliceTo (s.sliceTo pos).endPos = pos := by
  simp [Pos.ext_iff]

theorem Pos.ofSliceTo_inj {s : String} {p₀ : s.Pos} {pos pos' : (s.sliceTo p₀).Pos} :
    ofSliceTo pos = ofSliceTo pos' ↔ pos = pos' := by
  simp [Pos.ext_iff, Slice.Pos.ext_iff]

@[simp]
theorem Pos.ofSliceTo_le {s : String} {p₀ : s.Pos} {pos : (s.sliceTo p₀).Pos} :
    ofSliceTo pos ≤ p₀ := by
  simpa [Pos.le_iff, Pos.Raw.le_iff] using pos.isValidForSlice.le_utf8ByteSize

@[simp]
theorem Slice.Pos.ofSliceTo_le {s : Slice} {p₀ : s.Pos} {pos : (s.sliceTo p₀).Pos} :
    ofSliceTo pos ≤ p₀ := by
  simpa [Pos.le_iff, Pos.Raw.le_iff] using pos.isValidForSlice.le_utf8ByteSize

@[simp]
theorem Pos.ofSliceTo_lt_ofSliceTo_iff {s : String} {p : s.Pos}
    {q r : (s.sliceTo p).Pos} : Pos.ofSliceTo q < Pos.ofSliceTo r ↔ q < r := by
  simp [Pos.lt_iff, Slice.Pos.lt_iff, Pos.Raw.lt_iff]

@[simp]
theorem Pos.ofSliceTo_le_ofSliceTo_iff {s : String} {p : s.Pos}
    {q r : (s.sliceTo p).Pos} : Pos.ofSliceTo q ≤ Pos.ofSliceTo r ↔ q ≤ r := by
  simp [Pos.le_iff, Slice.Pos.le_iff, Pos.Raw.le_iff]

/-- Given a position in `s` that is at most `p₀`, obtain the corresponding position in `s.sliceTo p₀`. -/
@[inline]
def Pos.sliceTo {s : String} (p₀ : s.Pos) (pos : s.Pos) (h : pos ≤ p₀) :
    (s.sliceTo p₀).Pos where
  offset := pos.offset
  isValidForSlice := Pos.Raw.isValidForSlice_stringSliceTo.2 ⟨h, pos.isValid⟩

@[deprecated Pos.sliceTo (since := "2025-11-20")]
def Pos.toReplaceEnd {s : String} (p₀ : s.Pos) (pos : s.Pos) (h : pos ≤ p₀) :
    (s.sliceTo p₀).Pos :=
  sliceTo p₀ pos h

@[simp]
theorem Pos.offset_sliceTo {s : String} {p₀ : s.Pos} {pos : s.Pos} {h : pos ≤ p₀} :
    (sliceTo p₀ pos h).offset = pos.offset := (rfl)

@[simp]
theorem Pos.sliceTo_inj {s : String} {p₀ : s.Pos} {pos pos' : s.Pos} {h h'} :
    p₀.sliceTo pos h = p₀.sliceTo pos' h' ↔ pos = pos' := by
  simp [Pos.ext_iff, Slice.Pos.ext_iff]

@[simp]
theorem Slice.Pos.ofSliceTo_sliceTo {s : Slice} {p₀ p : s.Pos} {h : p ≤ p₀} :
    Slice.Pos.ofSliceTo (p₀.sliceTo p h) = p := by
  simp [Pos.ext_iff]

@[simp]
theorem Slice.Pos.sliceTo_ofSliceTo {s : Slice} {p₀ : s.Pos} {p : (s.sliceTo p₀).Pos} :
    p₀.sliceTo (Slice.Pos.ofSliceTo p) Slice.Pos.ofSliceTo_le = p := by
  simp [← Slice.Pos.ofSliceTo_inj]

@[simp]
theorem Pos.ofSliceTo_sliceTo {s : String} {p₀ p : s.Pos} {h : p ≤ p₀} :
    Pos.ofSliceTo (p₀.sliceTo p h) = p := by
  simp [Pos.ext_iff]

@[simp]
theorem Pos.sliceTo_ofSliceTo {s : String} {p₀ : s.Pos} {p : (s.sliceTo p₀).Pos} :
    p₀.sliceTo (Pos.ofSliceTo p) Pos.ofSliceTo_le = p := by
  simp [← Pos.ofSliceTo_inj]

theorem Pos.Raw.isValidForSlice_slice {s : Slice} {p₀ p₁ : s.Pos} {h} (pos : Pos.Raw) :
    pos.IsValidForSlice (s.slice p₀ p₁ h) ↔
      pos.offsetBy p₀.offset ≤ p₁.offset ∧ (pos.offsetBy p₀.offset).IsValidForSlice s := by
  refine ⟨fun ⟨h₁, h₂⟩ => ?_, fun ⟨h₁, h₂⟩ => ⟨?_, ?_⟩⟩
  · have : pos.offsetBy p₀.offset ≤ p₁.offset := by
      simp [Slice.Pos.le_iff, Pos.Raw.le_iff, Slice.utf8ByteSize_eq] at h h₁ ⊢
      omega
    exact ⟨this, ⟨Pos.Raw.le_trans this p₁.isValidForSlice.le_rawEndPos, by simpa [offsetBy_assoc]⟩⟩
  · simp [Slice.Pos.le_iff, Pos.Raw.le_iff, Slice.utf8ByteSize_eq] at h h₁ ⊢
    omega
  · simpa [offsetBy_assoc] using h₂.isValid_offsetBy

theorem Pos.Raw.isValidForSlice_stringSlice {s : String} {p₀ p₁ : s.Pos} {h} (pos : Pos.Raw) :
    pos.IsValidForSlice (s.slice p₀ p₁ h) ↔
      pos.offsetBy p₀.offset ≤ p₁.offset ∧ (pos.offsetBy p₀.offset).IsValid s := by
  simp [← slice_toSlice, isValidForSlice_slice]

/-- Given a position in `s.slice p₀ p₁ h`, obtain the corresponding position in `s`. -/
@[inline]
def Slice.Pos.ofSlice {s : Slice} {p₀ p₁ : s.Pos} {h} (pos : (s.slice p₀ p₁ h).Pos) : s.Pos where
  offset := pos.offset.offsetBy p₀.offset
  isValidForSlice := (Pos.Raw.isValidForSlice_slice _).1 pos.isValidForSlice |>.2

@[simp]
theorem Slice.Pos.offset_ofSlice {s : Slice} {p₀ p₁ : s.Pos} {h} {pos : (s.slice p₀ p₁ h).Pos} :
    (Pos.ofSlice pos).offset = pos.offset.offsetBy p₀.offset := (rfl)

@[simp]
theorem Slice.Pos.ofSlice_startPos {s : Slice} {p₀ p₁ : s.Pos} {h} :
    ofSlice (s.slice p₀ p₁ h).startPos = p₀ := by
  simp [Pos.ext_iff]

@[simp]
theorem Slice.Pos.offset_add_slice {s : Slice} {p₀ p₁ : s.Pos} {h} :
    p₀.offset + s.slice p₀ p₁ h = p₁.offset := by
  simp [Pos.Raw.ext_iff, Pos.Raw.byteDistance_eq, Pos.le_iff, Pos.Raw.le_iff] at ⊢ h
  omega

@[simp]
theorem Slice.Pos.ofSlice_endPos {s : Slice} {p₀ p₁ : s.Pos} {h} :
    ofSlice (s.slice p₀ p₁ h).endPos = p₁ := by
  simp [Pos.ext_iff]

@[simp]
theorem Slice.Pos.ofSlice_inj {s : Slice} {p₀ p₁ : s.Pos} {h} (pos₁ pos₂ : (s.slice p₀ p₁ h).Pos) :
    ofSlice pos₁ = ofSlice pos₂ ↔ pos₁ = pos₂ := by
  simp [Pos.ext_iff, Pos.Raw.ext_iff]

@[simp]
theorem Slice.Pos.le_ofSlice {s : Slice} {p₀ p₁ : s.Pos} {h}
    {pos : (s.slice p₀ p₁ h).Pos} : p₀ ≤ ofSlice pos := by
  simp [Pos.le_iff, Pos.Raw.le_iff]

@[simp]
theorem Slice.Pos.ofSlice_le {s : Slice} {p₀ p₁ : s.Pos} {h}
    {pos : (s.slice p₀ p₁ h).Pos} : ofSlice pos ≤ p₁ := by
  have := (Pos.Raw.isValidForSlice_slice _).1 pos.isValidForSlice |>.1
  simpa [Pos.le_iff, Pos.Raw.le_iff]

@[simp]
theorem Slice.Pos.ofSlice_lt_ofSlice_iff {s : Slice} {p₀ p₁ : s.Pos} {h}
    {q r : (s.slice p₀ p₁ h).Pos} : Slice.Pos.ofSlice q < Slice.Pos.ofSlice r ↔ q < r := by
  simp [Slice.Pos.lt_iff, Pos.Raw.lt_iff]

@[simp]
theorem Slice.Pos.ofSlice_le_ofSlice_iff {s : Slice} {p₀ p₁ : s.Pos} {h}
    {q r : (s.slice p₀ p₁ h).Pos} : Slice.Pos.ofSlice q ≤ Slice.Pos.ofSlice r ↔ q ≤ r := by
  simp [Slice.Pos.le_iff, Pos.Raw.le_iff]

/-- Given a position in `s.slice p₀ p₁ h`, obtain the corresponding position in `s`. -/
@[inline]
def Pos.ofSlice {s : String} {p₀ p₁ : s.Pos} {h} (pos : (s.slice p₀ p₁ h).Pos) : s.Pos :=
  ofToSlice (Slice.Pos.ofSlice pos)

@[simp]
theorem Pos.offset_ofSlice {s : String} {p₀ p₁ : s.Pos} {h} {pos : (s.slice p₀ p₁ h).Pos} :
    (Pos.ofSlice pos).offset = pos.offset.offsetBy p₀.offset := (rfl)

@[simp]
theorem Pos.ofSlice_startPos {s : String} {p₀ p₁ : s.Pos} {h} :
    ofSlice (s.slice p₀ p₁ h).startPos = p₀ := by
  simp [Pos.ext_iff]

@[simp]
theorem Pos.offset_add_slice {s : String} {p₀ p₁ : s.Pos} {h} :
    p₀.offset + s.slice p₀ p₁ h = p₁.offset := by
  simp [Pos.Raw.ext_iff, Pos.le_iff, Pos.Raw.le_iff] at ⊢ h
  omega

@[simp]
theorem Pos.ofSlice_endPos {s : String} {p₀ p₁ : s.Pos} {h} :
    ofSlice (s.slice p₀ p₁ h).endPos = p₁ := by
  simp [Pos.ext_iff]

@[simp]
theorem Pos.ofSlice_inj {s : String} {p₀ p₁ : s.Pos} {h} (pos₁ pos₂ : (s.slice p₀ p₁ h).Pos) :
    ofSlice pos₁ = ofSlice pos₂ ↔ pos₁ = pos₂ := by
  simp [Pos.ext_iff, Pos.Raw.ext_iff, Slice.Pos.ext_iff]

@[simp]
theorem Pos.le_ofSlice {s : String} {p₀ p₁ : s.Pos} {h}
    {pos : (s.slice p₀ p₁ h).Pos} : p₀ ≤ ofSlice pos := by
  simp [Pos.le_iff, Pos.Raw.le_iff]

@[simp]
theorem Pos.ofSlice_le {s : String} {p₀ p₁ : s.Pos} {h}
    {pos : (s.slice p₀ p₁ h).Pos} : ofSlice pos ≤ p₁ := by
  have := (Pos.Raw.isValidForSlice_slice _).1 pos.isValidForSlice |>.1
  simpa [Pos.le_iff, Pos.Raw.le_iff]

@[simp]
theorem Pos.ofSlice_lt_ofSlice_iff {s : String} {p₀ p₁ : s.Pos} {h}
    {q r : (s.slice p₀ p₁ h).Pos} : Pos.ofSlice q < Pos.ofSlice r ↔ q < r := by
  simp [Pos.lt_iff, Slice.Pos.lt_iff, Pos.Raw.lt_iff]

@[simp]
theorem Pos.ofSlice_le_ofSlice_iff {s : String} {p₀ p₁ : s.Pos} {h}
    {q r : (s.slice p₀ p₁ h).Pos} : Pos.ofSlice q ≤ Pos.ofSlice r ↔ q ≤ r := by
  simp [Pos.le_iff, Slice.Pos.le_iff, Pos.Raw.le_iff]

theorem Slice.Pos.le_trans {s : Slice} {p q r : s.Pos} : p ≤ q → q ≤ r → p ≤ r := by
  simpa [Pos.le_iff, Pos.Raw.le_iff] using Nat.le_trans

/-- Given a position in `s` that is between `p₀` and `p₁`, obtain the corresponding position in
`s.slice p₀ p₁ h`. -/
@[inline]
def Slice.Pos.slice {s : Slice} (pos : s.Pos) (p₀ p₁ : s.Pos) (h₁ : p₀ ≤ pos) (h₂ : pos ≤ p₁) :
    (s.slice p₀ p₁ (Slice.Pos.le_trans h₁ h₂)).Pos where
  offset := pos.offset.unoffsetBy p₀.offset
  isValidForSlice := (Pos.Raw.isValidForSlice_slice _).2
    (by simp [Pos.Raw.offsetBy_unoffsetBy_of_le h₁, Slice.Pos.le_iff.1 h₂, pos.isValidForSlice])

/-- Given a position in `s` that is between `p₀` and `p₁`, obtain the corresponding position in
`s.slice p₀ p₁ h`. -/
@[inline]
def Pos.slice {s : String} (pos : s.Pos) (p₀ p₁ : s.Pos) (h₁ : p₀ ≤ pos) (h₂ : pos ≤ p₁) :
    (s.slice p₀ p₁ (Pos.le_trans h₁ h₂)).Pos :=
  Slice.Pos.slice pos.toSlice _ _ h₁ h₂

@[simp]
theorem Pos.offset_slice {s : String} {p₀ p₁ pos : s.Pos} {h₁ : p₀ ≤ pos} {h₂ : pos ≤ p₁} :
    (pos.slice p₀ p₁ h₁ h₂).offset = pos.offset.unoffsetBy p₀.offset := (rfl)

@[simp]
theorem Slice.Pos.offset_slice {s : Slice} {p₀ p₁ pos : s.Pos} {h₁ : p₀ ≤ pos} {h₂ : pos ≤ p₁} :
    (pos.slice p₀ p₁ h₁ h₂).offset = pos.offset.unoffsetBy p₀.offset := (rfl)

@[simp]
theorem Slice.Pos.ofSlice_slice {s : Slice} {p₀ p₁ pos : s.Pos}
    {h₁ : p₀ ≤ pos} {h₂ : pos ≤ p₁} :
    Slice.Pos.ofSlice (pos.slice p₀ p₁ h₁ h₂) = pos := by
  simpa [Pos.ext_iff] using Pos.Raw.offsetBy_unoffsetBy_of_le h₁

@[simp]
theorem Slice.Pos.slice_ofSlice {s : Slice} {p₀ p₁ : s.Pos} {h}
    {pos : (s.slice p₀ p₁ h).Pos} :
    (Slice.Pos.ofSlice pos).slice p₀ p₁ Slice.Pos.le_ofSlice Slice.Pos.ofSlice_le = pos := by
  simp [← Slice.Pos.ofSlice_inj]

@[simp]
theorem Pos.ofSlice_slice {s : String} {p₀ p₁ pos : s.Pos}
    {h₁ : p₀ ≤ pos} {h₂ : pos ≤ p₁} :
    Pos.ofSlice (pos.slice p₀ p₁ h₁ h₂) = pos := by
  simpa [Pos.ext_iff] using Pos.Raw.offsetBy_unoffsetBy_of_le h₁

@[simp]
theorem Pos.slice_ofSlice {s : String} {p₀ p₁ : s.Pos} {h}
    {pos : (s.slice p₀ p₁ h).Pos} :
    (Pos.ofSlice pos).slice p₀ p₁ Pos.le_ofSlice Pos.ofSlice_le = pos := by
  simp [← Pos.ofSlice_inj]

@[simp]
theorem Slice.Pos.slice_inj {s : Slice} {p₀ p₁ : s.Pos} {pos pos' : s.Pos}
    {h₁ h₁' h₂ h₂'} :
    pos.slice p₀ p₁ h₁ h₂ = pos'.slice p₀ p₁ h₁' h₂' ↔ pos = pos' := by
  simp [Pos.ext_iff, Pos.Raw.ext_iff, Pos.le_iff, Pos.Raw.le_iff] at ⊢ h₁ h₁'
  omega

@[simp]
theorem Pos.slice_inj {s : String} {p₀ p₁ : s.Pos} {pos pos' : s.Pos}
    {h₁ h₁' h₂ h₂'} :
    pos.slice p₀ p₁ h₁ h₂ = pos'.slice p₀ p₁ h₁' h₂' ↔ pos = pos' := by
  simp [Pos.ext_iff, Pos.Raw.ext_iff, Slice.Pos.ext_iff, Pos.le_iff, Pos.Raw.le_iff] at ⊢ h₁ h₁'
  omega

/--
Given a position in `s`, obtain the corresponding position in `s.slice p₀ p₁ h`, or panic if `pos`
is not between `p₀` and `p₁`.
-/
@[inline]
def Slice.Pos.sliceOrPanic {s : Slice} (pos : s.Pos) (p₀ p₁ : s.Pos) {h} :
    (s.slice p₀ p₁ h).Pos :=
  if h : p₀ ≤ pos ∧ pos ≤ p₁ then
    pos.slice p₀ p₁ h.1 h.2
  else
    panic! "Position is outside of the bounds of the slice."

/--
Given a position in `s`, obtain the corresponding position in `s.slice p₀ p₁ h`, or panic if `pos`
is not between `p₀` and `p₁`.
-/
@[inline]
def Pos.sliceOrPanic {s : String} (pos : s.Pos) (p₀ p₁ : s.Pos) {h} :
    (s.slice p₀ p₁ h).Pos :=
  Slice.Pos.sliceOrPanic pos.toSlice _ _

theorem Slice.slice_eq_slice! {s : Slice} {p₀ p₁ h} : s.slice p₀ p₁ h = s.slice! p₀ p₁ := by
  simp [slice!, h]

theorem slice_eq_slice! {s : String} {p₀ p₁ h} : s.slice p₀ p₁ h = s.slice! p₀ p₁ := by
  simp [slice!, slice, Slice.slice_eq_slice!]

/-- Given a position in `s.slice! p₀ p₁`, obtain the corresponding position in `s`, or panic if
taking `s.slice! p₀ p₁` already panicked. -/
@[inline]
def Slice.Pos.ofSlice! {s : Slice} {p₀ p₁ : s.Pos} (pos : (s.slice! p₀ p₁).Pos) : s.Pos :=
  if h : p₀ ≤ p₁ then
    ofSlice (h := h) (pos.cast (congrArg Slice.copy slice_eq_slice!.symm))
  else
    panic! "Starting position must be less than or equal to end position."

/-- Given a position in `s.slice! p₀ p₁`, obtain the corresponding position in `s`, or panic if
taking `s.slice! p₀ p₁` already panicked. -/
@[inline]
def Pos.ofSlice! {s : String} {p₀ p₁ : s.Pos} (pos : (s.slice! p₀ p₁).Pos) : s.Pos :=
  ofToSlice (Slice.Pos.ofSlice! pos)

/--
Given a position in `s`, obtain the corresponding position in `s.slice! p₀ p₁ h`, or panic if
taking `s.slice! p₀ p₁` already panicked or if the position is not between `p₀` and `p₁`.
-/
@[inline]
def Slice.Pos.slice! {s : Slice} (pos : s.Pos) (p₀ p₁ : s.Pos) :
    (s.slice! p₀ p₁).Pos :=
  if h : p₀ ≤ pos ∧ pos ≤ p₁ then
    (pos.slice _ _ h.1 h.2).cast (congrArg Slice.copy slice_eq_slice!)
  else
    panic! "Starting position must be less than or equal to end position and position must be between starting position and end position."

/--
Given a position in `s`, obtain the corresponding position in `s.slice! p₀ p₁ h`, or panic if
taking `s.slice! p₀ p₁` already panicked or if the position is not between `p₀` and `p₁`.
-/
@[inline]
def Pos.slice! {s : String} (pos : s.Pos) (p₀ p₁ : s.Pos) :
    (s.slice! p₀ p₁).Pos :=
  Slice.Pos.slice! pos.toSlice _ _

theorem extract_eq_copy_slice {s : String} (p₀ p₁ : s.Pos) (h : p₀ ≤ p₁) :
    s.extract p₀ p₁ = (s.slice p₀ p₁ h).copy := by
  simp [← toByteArray_inj, Slice.toByteArray_copy]

/--
Copies a region of a slice to a new string.

The region of `s` from `b` (inclusive) to `e` (exclusive) is copied to a newly-allocated `String`.

If `b`'s offset is greater than or equal to that of `e`, then the resulting string is `""`.

If possible, prefer `Slice.slice`, which avoids the allocation.
-/
@[inline]
def Slice.extract (s : Slice) (p₀ p₁ : s.Pos) : String :=
  s.str.extract p₀.str p₁.str

@[simp]
theorem Slice.Pos.str_le_str_iff {s : Slice} {p q : s.Pos} : p.str ≤ q.str ↔ p ≤ q := by
  simp [String.Pos.le_iff, Slice.Pos.le_iff, Pos.Raw.le_iff]

@[simp]
theorem Slice.Pos.str_lt_str_iff {s : Slice} {p q : s.Pos} : p.str < q.str ↔ p < q := by
  simp [String.Pos.lt_iff, Slice.Pos.lt_iff, Pos.Raw.lt_iff]

theorem Slice.extract_eq_copy_slice {s : Slice} (p₀ p₁ : s.Pos) (h : p₀ ≤ p₁) :
    s.extract p₀ p₁ = (s.slice p₀ p₁ h).copy := by
  simp [← toByteArray_inj, Slice.toByteArray_copy, Slice.extract]

/--
Advances the position `p` `n` times.

If this would move `p` past the end of `s`, the result is `s.endPos`.
-/
def Slice.Pos.nextn {s : Slice} (p : s.Pos) (n : Nat) : s.Pos :=
  match n with
  | 0 => p
  | n + 1 =>
    if h : p ≠ s.endPos then
      nextn (p.next h) n
    else
      p

/--
Advances the position `p` `n` times.

If this would move `p` past the end of `s`, the result is `s.endPos`.
-/
@[inline]
def Pos.nextn {s : String} (p : s.Pos) (n : Nat) : s.Pos :=
  ofToSlice (p.toSlice.nextn n)


theorem Slice.Pos.le_nextn {s : Slice} {p : s.Pos} {n : Nat} : p ≤ p.nextn n := by
  fun_induction nextn with
  | case1 => simp
  | case2 p n h ih =>
    simp only [Pos.le_iff] at *
    exact Pos.Raw.le_of_lt (Pos.Raw.lt_of_lt_of_le lt_next ih)
  | case3 => simp

theorem Pos.le_nextn {s : String} {p : s.Pos} {n : Nat} :
    p ≤ p.nextn n := by
  simpa [nextn, Pos.le_iff, ← offset_toSlice] using Slice.Pos.le_nextn

/--
Returns the next position in a string after position `p`. If `p` is not a valid position or
`p = s.endPos`, returns the position one byte after `p`.

A run-time bounds check is performed to determine whether `p` is at the end of the string. If a
bounds check has already been performed, use `String.next'` to avoid a repeated check.

This is a legacy function. The recommended alternative is `String.Pos.next` or one of its
variants like `String.Pos.next?`, combined with `String.pos` or another means of obtaining
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

This is a legacy function. The recommended alternative is `String.Pos.prev` or one of its
variants like `String.Pos.prev?`, combined with `String.pos` or another means of obtaining
a `String.Pos`.

Examples:
* `"abc".get ("abc".rawEndPos |> "abc".prev) = 'c'`
* `"L∃∀N".get ("L∃∀N".rawEndPos |> "L∃∀N".prev |> "L∃∀N".prev |> "L∃∀N".prev) = '∃'`
-/
@[extern "lean_string_utf8_prev", expose]
def Pos.Raw.prev : (@& String) → (@& Pos.Raw) → Pos.Raw
  | s, p => utf8PrevAux s.toList 0 p

@[extern "lean_string_utf8_prev", expose, deprecated Pos.Raw.prev (since := "2025-10-14")]
def prev : (@& String) → (@& Pos.Raw) → Pos.Raw
  | s, p => Pos.Raw.utf8PrevAux s.toList 0 p

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

This is a legacy function. The recommended alternative is `String.Pos.get`, combined with
`String.pos` or another means of obtaining a `String.Pos`.

Examples:
* `"abc".get' 0 (by decide) = 'a'`
* `let lean := "L∃∀N"; lean.get' (0 |> lean.next |> lean.next) (by decide) = '∀'`
-/
@[extern "lean_string_utf8_get_fast", expose]
def Pos.Raw.get' (s : @& String) (p : @& Pos.Raw) (h : ¬ p.atEnd s) : Char :=
  match s with
  | s => Pos.Raw.utf8GetAux s.toList 0 p

@[extern "lean_string_utf8_get_fast", expose, deprecated Pos.Raw.get' (since := "2025-10-14")]
def get' (s : @& String) (p : @& Pos.Raw) (h : ¬ p.atEnd s) : Char :=
  match s with
  | s => Pos.Raw.utf8GetAux s.toList 0 p

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

This is a legacy function. The recommended alternative is `String.Pos.next`, combined with
`String.pos` or another means of obtaining a `String.Pos`.

Example:
* `let abc := "abc"; abc.get (abc.next' 0 (by decide)) = 'b'`
-/
@[extern "lean_string_utf8_next_fast", expose, tagged_return]
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

This is a legacy function. The recommended alternative is `String.Pos.extract`, but usually
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
  | s, b, e => if b.byteIdx ≥ e.byteIdx then "" else ofList (go₁ s.toList 0 b e)
where
  go₁ : List Char → Pos.Raw → Pos.Raw → Pos.Raw → List Char
    | [],        _, _, _ => []
    | s@(c::cs), i, b, e => if i = b then go₂ s i e else go₁ cs (i + c) b e

  go₂ : List Char → Pos.Raw → Pos.Raw → List Char
    | [],    _, _ => []
    | c::cs, i, e => if i = e then [] else c :: go₂ cs (i + c) e

def Pos.Raw.offsetOfPosAux (s : String) (pos : Pos.Raw) (i : Pos.Raw) (offset : Nat) : Nat :=
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
@[inline] def Pos.Raw.offsetOfPos (s : String) (pos : Pos.Raw) : Nat :=
  offsetOfPosAux s pos 0 0

@[deprecated String.Pos.Raw.offsetOfPos (since := "2025-11-17")]
def offsetOfPos (s : String) (pos : Pos.Raw) : Nat :=
  pos.offsetOfPos s

@[export lean_string_offsetofpos]
def Internal.offsetOfPosImpl (s : String) (pos : Pos.Raw) : Nat :=
  String.Pos.Raw.offsetOfPos s pos

theorem Pos.Raw.utf8SetAux_of_gt (c' : Char) : ∀ (cs : List Char) {i p : Pos.Raw}, i > p → utf8SetAux c' cs i p = cs
  | [],    _, _, _ => rfl
  | c::cs, i, p, h => by
    rw [utf8SetAux, if_neg (mt (congrArg (·.1)) (Ne.symm <| Nat.ne_of_lt h)), utf8SetAux_of_gt c' cs]
    exact Nat.lt_of_lt_of_le h (Nat.le_add_right ..)

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

end String

namespace String

@[ext]
theorem ext {s₁ s₂ : String} (h : s₁.toList = s₂.toList) : s₁ = s₂ :=
  toList_injective h

@[simp] theorem length_empty : "".length = 0 := by simp [← length_toList, toList_empty]

@[deprecated singleton_eq_ofList (since := "2025-10-30")]
theorem singleton_eq {c : Char} : String.singleton c = ofList [c] :=
  singleton_eq_ofList

@[simp] theorem toList_singleton (c : Char) : (String.singleton c).toList = [c] := by
  simp [singleton_eq_ofList]

@[deprecated toList_singleton (since := "2025-10-30")]
theorem data_singleton (c : Char) : (String.singleton c).toList = [c] :=
  toList_singleton c

@[simp]
theorem length_singleton {c : Char} : (String.singleton c).length = 1 := by
  simp [← length_toList]

@[simp]
theorem toList_push (c : Char) : (String.push s c).toList = s.toList ++ [c] := by
  simp [← append_singleton]

@[deprecated toList_push (since := "2025-10-30")]
theorem data_push (c : Char) : (String.push s c).toList = s.toList ++ [c] :=
  toList_push c

@[simp] theorem length_push (c : Char) : (String.push s c).length = s.length + 1 := by
  simp [← length_toList]

@[simp] theorem length_pushn (c : Char) (n : Nat) : (pushn s c n).length = s.length + n := by
  rw [pushn_eq_repeat_push]; induction n <;> simp [Nat.repeat, Nat.add_assoc, *]

@[simp] theorem length_append (s t : String) : (s ++ t).length = s.length + t.length := by
  simp [← length_toList]

theorem lt_iff {s t : String} : s < t ↔ s.toList < t.toList := .rfl

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
  cases s.toList <;> simp [utf8PrevAux, Pos.Raw.le_iff]

@[deprecated Pos.Raw.prev_zero (since := "2025-10-10")]
theorem prev_zero (s : String) : (0 : Pos.Raw).prev s = 0 := by
  exact Pos.Raw.prev_zero s

@[deprecated Pos.Raw.get'_eq (since := "2025-10-14")]
theorem get'_eq (s : String) (p : Pos.Raw) (h) : p.get' s h = p.get s := rfl

@[deprecated Pos.Raw.next'_eq (since := "2025-10-14")]
theorem next'_eq (s : String) (p : Pos.Raw) (h) : p.next' s h = p.next s := rfl

-- `toRawSubstring'` is just a synonym for `toRawSubstring` without the `@[inline]` attribute
-- so for proving can be unfolded.
attribute [simp] toRawSubstring'

@[deprecated String.size_toByteArray (since := "2025-11-24")]
theorem size_bytes {s : String} : s.toByteArray.size = s.utf8ByteSize :=
  size_toByteArray

@[deprecated String.toByteArray_ofList (since := "2025-11-24")]
theorem bytes_ofList {l : List Char} : (ofList l).toByteArray = l.utf8Encode :=
  toByteArray_ofList

@[deprecated String.toByteArray_inj (since := "2025-11-24")]
theorem bytes_inj {s t : String} : s.toByteArray = t.toByteArray ↔ s = t :=
  toByteArray_inj

end String

namespace Char

@[deprecated String.length_singleton (since := "2026-02-12")]
theorem length_toString (c : Char) : c.toString.length = 1 := by
  simp

end Char
