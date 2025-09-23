/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Mario Carneiro
-/
module

prelude
public import Init.Data.List.Basic
public import Init.Data.Char.Basic
public import Init.Data.String.Bootstrap
public import Init.Data.ByteArray.Basic
public import Init.Data.String.Decode
import Init.Data.ByteArray.Lemmas

public section

universe u

section

@[simp]
theorem List.utf8Encode_nil : List.utf8Encode [] = ByteArray.empty := by simp [utf8Encode]

theorem List.utf8Encode_singleton {c : Char} : [c].utf8Encode = (String.utf8EncodeChar c).toByteArray := by
  simp [utf8Encode]

@[simp]
theorem List.utf8Encode_append {l l' : List Char} :
    (l ++ l').utf8Encode = l.utf8Encode ++ l'.utf8Encode := by
  simp [utf8Encode]

theorem List.utf8Encode_cons {c : Char} {l : List Char} : (c :: l).utf8Encode = [c].utf8Encode ++ l.utf8Encode := by
  rw [← singleton_append, List.utf8Encode_append]

theorem List.isUtf8FirstByte_getElem_utf8Encode_singleton {c : Char} {i : Nat} {hi : i < [c].utf8Encode.size} :
    UInt8.IsUtf8FirstByte [c].utf8Encode[i] ↔ i = 0 := by
  simp [List.utf8Encode_singleton, UInt8.isUtf8FirstByte_getElem_utf8EncodeChar]

@[simp]
theorem String.utf8EncodeChar_ne_nil {c : Char} : String.utf8EncodeChar c ≠ [] := by
  fun_cases String.utf8EncodeChar with simp

@[simp]
theorem List.utf8Encode_eq_empty {l : List Char} : l.utf8Encode = ByteArray.empty ↔ l = [] := by
  simp [utf8Encode, ← List.eq_nil_iff_forall_not_mem]

theorem ByteArray.isValidUtf8_utf8Encode {l : List Char} : IsValidUtf8 l.utf8Encode :=
  .intro l rfl

@[simp]
theorem ByteArray.isValidUtf8_empty : IsValidUtf8 ByteArray.empty :=
  .intro [] (by simp)

theorem Char.isValidUtf8_toByteArray_utf8EncodeChar {c : Char} :
    ByteArray.IsValidUtf8 (String.utf8EncodeChar c).toByteArray :=
  .intro [c] (by simp [List.utf8Encode_singleton])

theorem ByteArray.IsValidUtf8.append {b b' : ByteArray} (h : IsValidUtf8 b) (h' : IsValidUtf8 b') :
    IsValidUtf8 (b ++ b') := by
  rcases h with ⟨m, rfl⟩
  rcases h' with ⟨m', rfl⟩
  exact .intro (m ++ m') (by simp)

theorem ByteArray.isValidUtf8_utf8Encode_singleton_append_iff {b : ByteArray} {c : Char} :
    IsValidUtf8 ([c].utf8Encode ++ b) ↔ IsValidUtf8 b := by
  refine ⟨?_, fun h => IsValidUtf8.append isValidUtf8_utf8Encode h⟩
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
    exact hl ▸ isValidUtf8_utf8Encode

@[expose]
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
    (ByteArray.utf8Decode?.go b fuel i acc hi hf).isSome ↔ IsValidUtf8 (b.extract i b.size) := by
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
      ← List.utf8Encode_singleton, isValidUtf8_utf8Encode_singleton_append_iff]

theorem ByteArray.isSome_utf8Decode?_iff {b : ByteArray} :
    b.utf8Decode?.isSome ↔ IsValidUtf8 b := by
  rw [utf8Decode?, isSome_utf8Decode?go_iff, extract_zero_size]

@[simp]
theorem String.bytes_empty : "".bytes = ByteArray.empty := (rfl)

/--
Appends two strings. Usually accessed via the `++` operator.

The internal implementation will perform destructive updates if the string is not shared.

Examples:
 * `"abc".append "def" = "abcdef"`
 * `"abc" ++ "def" = "abcdef"`
 * `"" ++ "" = ""`
-/
@[extern "lean_string_append", expose]
def String.append (s : String) (t : @& String) : String where
  bytes := s.bytes ++ t.bytes
  isValidUtf8 := s.isValidUtf8.append t.isValidUtf8

instance : Append String where
  append s t := s.append t

@[simp]
theorem String.bytes_append {s t : String} : (s ++ t).bytes = s.bytes ++ t.bytes := (rfl)

theorem String.bytes_inj {s t : String} : s.bytes = t.bytes ↔ s = t := by
  refine ⟨fun h => ?_, (· ▸ rfl)⟩
  rcases s with ⟨s⟩
  rcases t with ⟨t⟩
  subst h
  rfl

@[simp]
theorem String.empty_append {s : String} : "" ++ s = s := by
  simp [← String.bytes_inj]

@[simp]
theorem String.append_empty {s : String} : s ++ "" = s := by
  simp [← String.bytes_inj]

@[simp] theorem List.bytes_asString {l : List Char} : l.asString.bytes = l.utf8Encode := by
  simp [List.asString, String.mk]

@[simp]
theorem List.asString_nil : List.asString [] = "" := by
  simp [← String.bytes_inj]

@[simp]
theorem List.asString_append {l₁ l₂ : List Char} : (l₁ ++ l₂).asString = l₁.asString ++ l₂.asString := by
  simp [← String.bytes_inj]

@[expose]
def String.Internal.toArray (b : String) : Array Char :=
  b.bytes.utf8Decode?.get (b.bytes.isSome_utf8Decode?_iff.2 b.isValidUtf8)

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

theorem String.exists_eq_asString (s : String) :
    ∃ l : List Char, s = l.asString := by
  rcases s with ⟨_, ⟨l, rfl⟩⟩
  refine ⟨l, by simp [← String.bytes_inj]⟩

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
theorem String.utf8ByteSize_empty : "".utf8ByteSize = 0 := (rfl)

@[simp]
theorem String.utf8ByteSize_append {s t : String} :
    (s ++ t).utf8ByteSize = s.utf8ByteSize + t.utf8ByteSize := by
  simp [utf8ByteSize]

@[simp]
theorem String.size_bytes {s : String} : s.bytes.size = s.utf8ByteSize := rfl

@[simp]
theorem String.bytes_push {s : String} {c : Char} : (s.push c).bytes = s.bytes ++ [c].utf8Encode := by
  simp [push]

-- This is just to keep the proof of `set_next_add` below from breaking; if that lemma goes away
-- or the proof is rewritten, it can be removed.
private noncomputable def String.utf8ByteSize' : String → Nat
  | s => go s.data
where
  go : List Char → Nat
  | []    => 0
  | c::cs => go cs + c.utf8Size

private theorem String.utf8ByteSize'_eq (s : String) : s.utf8ByteSize' = s.utf8ByteSize := by
  suffices ∀ l, utf8ByteSize'.go l = l.asString.utf8ByteSize by
    obtain ⟨m, rfl⟩ := s.exists_eq_asString
    rw [utf8ByteSize', this, asString_data]
  intro l
  induction l with
  | nil => simp [utf8ByteSize'.go]
  | cons c cs ih =>
    rw [utf8ByteSize'.go, ih, ← List.singleton_append, List.asString_append,
      utf8ByteSize_append, Nat.add_comm]
    congr
    rw [← size_bytes, List.bytes_asString, List.utf8Encode_singleton,
      List.size_toByteArray, length_utf8EncodeChar]

end

namespace String

instance : HAdd String.Pos String.Pos String.Pos where
  hAdd p₁ p₂ := { byteIdx := p₁.byteIdx + p₂.byteIdx }

instance : HSub String.Pos String.Pos String.Pos where
  hSub p₁ p₂ := { byteIdx :=  p₁.byteIdx - p₂.byteIdx }

@[export lean_string_pos_sub]
def Pos.Internal.subImpl : String.Pos → String.Pos → String.Pos :=
  (· - ·)

instance : HAdd String.Pos Char String.Pos where
  hAdd p c := { byteIdx := p.byteIdx + c.utf8Size }

instance : HAdd String.Pos String String.Pos where
  hAdd p s := { byteIdx := p.byteIdx + s.utf8ByteSize }

instance : LE String.Pos where
  le p₁ p₂ := p₁.byteIdx ≤ p₂.byteIdx

instance : LT String.Pos where
  lt p₁ p₂ := p₁.byteIdx < p₂.byteIdx

instance (p₁ p₂ : String.Pos) : Decidable (LE.le p₁ p₂) :=
  inferInstanceAs (Decidable (p₁.byteIdx ≤ p₂.byteIdx))

instance (p₁ p₂ : String.Pos) : Decidable (LT.lt p₁ p₂) :=
  inferInstanceAs (Decidable (p₁.byteIdx < p₂.byteIdx))

instance : Min String.Pos := minOfLe
instance : Max String.Pos := maxOfLe

theorem Pos.le_iff {i₁ i₂ : Pos} : i₁ ≤ i₂ ↔ i₁.byteIdx ≤ i₂.byteIdx := .rfl

theorem Pos.lt_iff {i₁ i₂ : Pos} : i₁ < i₂ ↔ i₁.byteIdx < i₂.byteIdx := .rfl

@[simp]
theorem byteIdx_endPos {s : String} : s.endPos.byteIdx = s.utf8ByteSize := rfl

@[simp]
theorem utf8ByteSize_ofByteArray {b : ByteArray} {h} :
    (String.ofByteArray b h).utf8ByteSize = b.size := rfl

attribute [ext] String.Pos

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
@[expose]
def toList (s : String) : List Char :=
  s.data

/--
Predicate for validity of positions inside a `String`.

There are multiple equivalent definitions for validity.

We say that a position is valid if the string obtained by taking all of the bytes up to, but
excluding, the given position, is valid UTF-8; see `Pos.isValid_iff_isValidUtf8_extract_zero`.

Similarly, a position is valid if the string obtained by taking all of the bytes starting at the
given position is valid UTF-8; see `Pos.isValid_iff_isValidUtf8_extract_utf8ByteSize`.

An equivalent condition is that the position is the length of the UTF-8 encoding of
some prefix of the characters of the string; see `Pos.isValid_iff_exists_append` and
`Pos.isValid_iff_exists_take_data`.

Another equivalent condition that can be checked efficiently is that the position is either the
end position or strictly smaller than the end position and the byte at the position satisfies
`UInt8.IsUtf8FirstByte`; see `Pos.isValid_iff_isUtf8FirstByte`.

Examples:
 * `String.Pos.IsValid "abc" ⟨0⟩`
 * `String.Pos.IsValid "abc" ⟨1⟩`
 * `String.Pos.IsValid "abc" ⟨3⟩`
 * `¬ String.Pos.IsValid "abc" ⟨4⟩`
 * `String.Pos.IsValid "𝒫(A)" ⟨0⟩`
 * `¬ String.Pos.IsValid "𝒫(A)" ⟨1⟩`
 * `¬ String.Pos.IsValid "𝒫(A)" ⟨2⟩`
 * `¬ String.Pos.IsValid "𝒫(A)" ⟨3⟩`
 * `String.Pos.IsValid "𝒫(A)" ⟨4⟩`
-/
structure Pos.IsValid (s : String) (off : String.Pos) : Prop where private mk ::
  le_endPos : off ≤ s.endPos
  isValidUtf8_extract_zero : (s.bytes.extract 0 off.byteIdx).IsValidUtf8

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
theorem Pos.IsValid.exists {s : String} {p : Pos} (h : p.IsValid s) :
    ∃ m₁ m₂ : List Char, m₁.utf8Encode = s.bytes.extract 0 p.byteIdx ∧ (m₁ ++ m₂).asString = s := by
  obtain ⟨l, hl⟩ := s.isValidUtf8
  obtain ⟨m₁, hm₁⟩ := h.isValidUtf8_extract_zero
  suffices m₁ <+: l by
    obtain ⟨m₂, rfl⟩ := this
    refine ⟨m₁, m₂, hm₁.symm, ?_⟩
    apply String.bytes_inj.1
    simpa using hl.symm
  apply List.isPrefix_of_utf8Encode_append_eq_utf8Encode (s.bytes.extract p.byteIdx s.bytes.size)
  rw [← hl, ← hm₁, ← ByteArray.extract_eq_extract_append_extract _ (by simp),
    ByteArray.extract_zero_size]
  simpa using h.le_endPos

theorem Pos.IsValid.isValidUtf8_extract_utf8ByteSize {s : String} {p : Pos} (h : p.IsValid s) :
    ByteArray.IsValidUtf8 (s.bytes.extract p.byteIdx s.utf8ByteSize) := by
  obtain ⟨m₁, m₂, hm, rfl⟩ := h.exists
  simp only [List.asString_append, bytes_append, List.bytes_asString]
  rw [ByteArray.extract_append_eq_right]
  · exact ByteArray.isValidUtf8_utf8Encode
  · rw [hm]
    simp only [List.asString_append, bytes_append, List.bytes_asString, ByteArray.size_extract,
      ByteArray.size_append, Nat.sub_zero]
    refine (Nat.min_eq_left ?_).symm
    simpa [utf8ByteSize, Pos.le_iff] using h.le_endPos
  · simp [utf8ByteSize]

theorem Pos.isValid_iff_exists_append {s : String} {p : Pos} :
    p.IsValid s ↔ ∃ s₁ s₂ : String, s = s₁ ++ s₂ ∧ p = s₁.endPos := by
  refine ⟨fun h => ⟨⟨_, h.isValidUtf8_extract_zero⟩, ⟨_, h.isValidUtf8_extract_utf8ByteSize⟩, ?_, ?_⟩, ?_⟩
  · apply String.bytes_inj.1
    have := Pos.le_iff.1 h.le_endPos
    simp_all [← size_bytes]
  · have := byteIdx_endPos ▸ Pos.le_iff.1 h.le_endPos
    apply String.Pos.ext
    simp [Nat.min_eq_left this]
  · rintro ⟨s₁, s₂, rfl, rfl⟩
    refine ⟨by simp [Pos.le_iff], ?_⟩
    simpa [ByteArray.extract_append_eq_left] using s₁.isValidUtf8

@[simp]
theorem Pos.byteIdx_zero : (0 : Pos).byteIdx = 0 := rfl

@[simp]
theorem Pos.isValid_zero {s : String} : (0 : Pos).IsValid s where
  le_endPos := by simp [Pos.le_iff]
  isValidUtf8_extract_zero := by simp

@[simp]
theorem Pos.isValid_endPos {s : String} : s.endPos.IsValid s where
  le_endPos := by simp [Pos.le_iff]
  isValidUtf8_extract_zero := by simp [← size_bytes, s.isValidUtf8]

@[simp]
theorem Pos.isValid_empty_iff {p : Pos} : p.IsValid "" ↔ p = 0 := by
  refine ⟨?_, ?_⟩
  · rintro ⟨h₁, h₂⟩
    simp only [le_iff, byteIdx_endPos, utf8ByteSize_empty, Nat.le_zero_eq] at h₁
    ext
    omega
  · rintro rfl
    simp

theorem Pos.isValid_asString {l : List Char} {p : Pos} :
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
    · simpa [Pos.ext_iff]

theorem Pos.isValid_iff_exists_take_data {s : String} {p : Pos} :
    p.IsValid s ↔ ∃ i, p.byteIdx = (s.data.take i).asString.utf8ByteSize := by
  obtain ⟨l, rfl⟩ := s.exists_eq_asString
  simp [isValid_asString]

@[simp]
theorem bytes_singleton {c : Char} : (String.singleton c).bytes = [c].utf8Encode := by
  simp [singleton]

theorem singleton_eq_asString {c : Char} : String.singleton c = [c].asString := by
  simp [← String.bytes_inj]

@[simp]
theorem utf8ByteSize_singleton {c : Char} : (String.singleton c).utf8ByteSize = c.utf8Size := by
  simp [← size_bytes, List.utf8Encode_singleton]

@[simp]
theorem Pos.isValid_singleton {c : Char} {p : Pos} :
    p.IsValid (String.singleton c) ↔ p = 0 ∨ p.byteIdx = c.utf8Size := by
  rw [singleton_eq_asString, Pos.isValid_asString]
  refine ⟨?_, ?_⟩
  · rintro ⟨i, hi'⟩
    obtain ⟨rfl, hi⟩ : i = 0 ∨ 1 ≤ i := by omega
    · simp [Pos.ext_iff, hi']
    · rw [hi', List.take_of_length_le (by simpa)]
      simp [← singleton_eq_asString]
  · rintro (rfl|hi)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp [hi, ← singleton_eq_asString]⟩

@[simp]
theorem Pos.byteIdx_sub {p₁ p₂ : Pos} : (p₁ - p₂).byteIdx = p₁.byteIdx - p₂.byteIdx := rfl

@[simp]
theorem Pos.byteIdx_add {p₁ p₂ : Pos} : (p₁ + p₂).byteIdx = p₁.byteIdx + p₂.byteIdx := rfl

@[simp]
theorem Pos.byteIdx_addChar {p : Pos} {c : Char} : (p + c).byteIdx = p.byteIdx + c.utf8Size := rfl

theorem Pos.isValid_append {s t : String} {p : Pos} :
    p.IsValid (s ++ t) ↔ p.IsValid s ∨ (s.endPos ≤ p ∧ (p - s.endPos).IsValid t) := by
  obtain ⟨s, rfl⟩ := exists_eq_asString s
  obtain ⟨t, rfl⟩ := exists_eq_asString t
  rw [← List.asString_append, Pos.isValid_asString, Pos.isValid_asString, Pos.isValid_asString]
  refine ⟨?_, ?_⟩
  · rintro ⟨j, hj⟩
    by_cases h : j ≤ s.length
    · exact Or.inl ⟨j, by simp [hj, List.take_append_of_le_length h]⟩
    · refine Or.inr ⟨?_, ⟨j - s.length, ?_⟩⟩
      · simp [Pos.le_iff, hj, List.take_append, List.take_of_length_le (i := j) (l := s) (by omega)]
      · simp [hj, List.take_append, List.take_of_length_le (i := j) (l := s) (by omega)]
  · rintro (⟨j, hj⟩|⟨h, ⟨j, hj⟩⟩)
    · refine ⟨min j s.length, ?_⟩
      rw [List.take_append_of_le_length (Nat.min_le_right ..), ← List.take_eq_take_min, hj]
    · refine ⟨s.length + j, ?_⟩
      simp only [Pos.byteIdx_sub, byteIdx_endPos, Pos.le_iff] at hj h
      simp only [List.take_append, List.take_of_length_le (i := s.length + j) (l := s) (by omega),
        Nat.add_sub_cancel_left, List.asString_append, utf8ByteSize_append]
      omega

theorem Pos.IsValid.append_left {t : String} {p : Pos} (h : p.IsValid t) (s : String) :
    (s.endPos + p).IsValid (s ++ t) :=
  isValid_append.2 (Or.inr ⟨by simp [Pos.le_iff], by
    suffices p = s.endPos + p - s.endPos by simp [← this, h]
    simp [Pos.ext_iff]⟩)

theorem Pos.IsValid.append_right {s : String} {p : Pos} (h : p.IsValid s) (t : String) :
    p.IsValid (s ++ t) :=
  isValid_append.2 (Or.inl h)

@[simp]
theorem append_singleton {s : String} {c : Char} : s ++ singleton c = s.push c := by
  simp [← bytes_inj]

theorem Pos.isValid_push {s : String} {c : Char} {p : Pos} :
    p.IsValid (s.push c) ↔ p.IsValid s ∨ p = s.endPos + c := by
  rw [← append_singleton, isValid_append, isValid_singleton]
  simp only [le_iff, byteIdx_endPos, Pos.ext_iff, byteIdx_sub, byteIdx_zero, byteIdx_addChar]
  refine ⟨?_, ?_⟩
  · rintro (h|⟨h₁,(h₂|h₂)⟩)
    · exact Or.inl h
    · suffices p = s.endPos by simp [this]
      simp only [Pos.ext_iff, byteIdx_endPos]
      omega
    · omega
  · rintro (h|h)
    · exact Or.inl h
    · omega

@[simp]
theorem utf8ByteSize_push {s : String} {c : Char} :
    (s.push c).utf8ByteSize = s.utf8ByteSize + c.utf8Size := by
  simp [← size_bytes, List.utf8Encode_singleton]

theorem endPos_push {s : String} {c : Char} : (s.push c).endPos = s.endPos + c := by
  simp [Pos.ext_iff]

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

/--
Accesses the indicated byte in the UTF-8 encoding of a string.

At runtime, this function is implemented by efficient, constant-time code.
-/
@[extern "lean_string_get_byte_fast", expose]
def getUtf8Byte (s : @& String) (p : Pos) (h : p < s.endPos) : UInt8 :=
  s.bytes[p.byteIdx]

@[simp]
theorem endPos_empty : "".endPos = 0 := rfl

theorem Pos.isValid_iff_isUtf8FirstByte {s : String} {p : Pos} :
    p.IsValid s ↔ p = s.endPos ∨ ∃ (h : p < s.endPos), (s.getUtf8Byte p h).IsUtf8FirstByte := by
  induction s using push_induction with
  | empty => simp [Pos.lt_iff]
  | push s c ih =>
    rw [isValid_push, ih]
    refine ⟨?_, ?_⟩
    · rintro ((rfl|⟨h, hb⟩)|h)
      · refine Or.inr ⟨by simp [Pos.lt_iff, Char.utf8Size_pos], ?_⟩
        simp only [getUtf8Byte, bytes_push, byteIdx_endPos]
        rw [ByteArray.getElem_append_right (by simp)]
        simp [List.isUtf8FirstByte_getElem_utf8Encode_singleton]
      · refine Or.inr ⟨by simp [lt_iff] at h ⊢; omega, ?_⟩
        simp only [getUtf8Byte, bytes_push]
        rwa [ByteArray.getElem_append_left, ← getUtf8Byte]
      · exact Or.inl (by simpa [endPos_push])
    · rintro (h|⟨h, hb⟩)
      · exact Or.inr (by simpa [endPos_push] using h)
      · simp only [getUtf8Byte, bytes_push] at hb
        by_cases h' : p < s.endPos
        · refine Or.inl (Or.inr ⟨h', ?_⟩)
          rwa [ByteArray.getElem_append_left h', ← getUtf8Byte] at hb
        · refine Or.inl (Or.inl ?_)
          rw [ByteArray.getElem_append_right (by simp [lt_iff] at h' ⊢; omega)] at hb
          simp only [size_bytes, List.isUtf8FirstByte_getElem_utf8Encode_singleton] at hb
          ext
          simp only [lt_iff, byteIdx_endPos, Nat.not_lt] at ⊢ h'
          omega

/--
Returns `true` if `p` is a valid UTF-8 position in the string `s`.

This means that `p ≤ s.endPos` and `p` lies on a UTF-8 character boundary. At runtime, this
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
def Pos.isValid (s : @&String) (p : @& Pos) : Bool :=
  if h : p < s.endPos then
    (s.getUtf8Byte p h).IsUtf8FirstByte
  else
    p = s.endPos

@[simp]
theorem Pos.isValid_eq_true_iff {s : String} {p : Pos} : p.isValid s = true ↔ p.IsValid s := by
  rw [isValid_iff_isUtf8FirstByte]
  fun_cases isValid s p with
  | case1 h =>
    simp_all only [decide_eq_true_eq, exists_true_left, iff_or_self]
    rintro rfl
    simp [lt_iff] at h
  | case2 => simp_all

@[simp]
theorem Pos.isValid_eq_false_iff {s : String} {p : Pos} : p.isValid s = false ↔ ¬ p.IsValid s := by
  rw [← Bool.not_eq_true, Pos.isValid_eq_true_iff]

instance {s : String} {p : Pos} : Decidable (p.IsValid s) :=
  decidable_of_iff (p.isValid s = true) Pos.isValid_eq_true_iff

theorem Pos.isValid_iff_isSome_utf8DecodeChar? {s : String} {p : Pos} :
    p.IsValid s ↔ p = s.endPos ∨ (s.bytes.utf8DecodeChar? p.byteIdx).isSome := by
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
      · simp [endPos_push]
  · refine isValid_iff_isUtf8FirstByte.2 (Or.inr ?_)
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 h
    refine ⟨?_, ?_⟩
    · have := ByteArray.le_size_of_utf8DecodeChar?_eq_some hc
      have := c.utf8Size_pos
      simp only [lt_iff, byteIdx_endPos, gt_iff_lt, ← size_bytes]
      omega
    · rw [getUtf8Byte]
      exact ByteArray.isUtf8FirstByte_of_isSome_utf8DecodeChar? h

theorem _root_.ByteArray.IsValidUtf8.isUtf8FirstByte_getElem_zero {b : ByteArray}
    (h : b.IsValidUtf8) (h₀ : 0 < b.size) : b[0].IsUtf8FirstByte := by
  rcases h with ⟨m, rfl⟩
  have : m ≠ [] := by
    rintro rfl
    simp at h₀
  conv => congr; congr; rw [← List.cons_head_tail this, ← List.singleton_append, List.utf8Encode_append]
  rw [ByteArray.getElem_append_left]
  · exact List.isUtf8FirstByte_getElem_utf8Encode_singleton.2 rfl
  · simp [List.utf8Encode_singleton, Char.utf8Size_pos]

theorem isUtf8FirstByte_getUtf8Byte_zero {b : String} {h} : (b.getUtf8Byte 0 h).IsUtf8FirstByte :=
  b.isValidUtf8.isUtf8FirstByte_getElem_zero _

protected theorem Pos.le_trans {a b c : Pos} : a ≤ b → b ≤ c → a ≤ c := by
  simpa [le_iff] using Nat.le_trans

protected theorem Pos.lt_of_lt_of_le {a b c : Pos} : a < b → b ≤ c → a < c := by
  simpa [le_iff, lt_iff] using Nat.lt_of_lt_of_le

theorem Pos.isValidUtf8_extract_iff {s : String} (p₁ p₂ : Pos) (hle : p₁ ≤ p₂) (hle' : p₂ ≤ s.endPos) :
    (s.bytes.extract p₁.byteIdx p₂.byteIdx).IsValidUtf8 ↔ p₁ = p₂ ∨ (p₁.IsValid s ∧ p₂.IsValid s) := by
  have hle'' : p₂.byteIdx ≤ s.bytes.size := by simpa [le_iff] using hle'
  refine ⟨fun h => Classical.or_iff_not_imp_left.2 (fun h' => ?_), ?_⟩
  · have hlt : p₁ < p₂ := by
      simp_all [le_iff, lt_iff, Pos.ext_iff]
      omega
    have h₁ : p₁.IsValid s := by
      rw [isValid_iff_isUtf8FirstByte]
      refine Or.inr ⟨Pos.lt_of_lt_of_le hlt hle', ?_⟩
      have hlt' : 0 < p₂.byteIdx - p₁.byteIdx := by
        simp [lt_iff] at hlt
        omega
      have := h.isUtf8FirstByte_getElem_zero
      simp only [ByteArray.size_extract, Nat.min_eq_left hle'', hlt', ByteArray.getElem_extract, Nat.add_zero] at this
      simp [getUtf8Byte, this trivial]
    refine ⟨h₁, ⟨hle', ?_⟩⟩
    rw [ByteArray.extract_eq_extract_append_extract p₁.byteIdx (by simp) hle]
    exact h₁.isValidUtf8_extract_zero.append h
  · refine fun h => h.elim (by rintro rfl; simp) (fun ⟨h₁, h₂⟩ => ?_)
    let t : String := ⟨_, h₂.isValidUtf8_extract_zero⟩
    have htb : t.bytes = s.bytes.extract 0 p₂.byteIdx := rfl
    have ht : p₁.IsValid t := by
      refine ⟨?_, ?_⟩
      · simpa [le_iff, t, Nat.min_eq_left hle'', ← size_bytes]
      · simpa [htb, ByteArray.extract_extract, Nat.min_eq_left (le_iff.1 hle)] using h₁.isValidUtf8_extract_zero
    simpa [htb, ByteArray.extract_extract, Nat.zero_add, Nat.min_eq_left hle'', ← size_bytes]
      using ht.isValidUtf8_extract_utf8ByteSize

theorem Pos.isValid_iff_isValidUtf8_extract_zero {s : String} {p : Pos} :
    p.IsValid s ↔ p ≤ s.endPos ∧ (s.bytes.extract 0 p.byteIdx).IsValidUtf8 :=
  ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩

theorem Pos.isValid_iff_isValidUtf8_extract_utf8ByteSize {s : String} {p : Pos} :
    p.IsValid s ↔ p ≤ s.endPos ∧ (s.bytes.extract p.byteIdx s.utf8ByteSize).IsValidUtf8 := by
  refine ⟨fun h => ⟨h.le_endPos, h.isValidUtf8_extract_utf8ByteSize⟩, fun ⟨h₁, h₂⟩ => ?_⟩
  rw [← byteIdx_endPos, isValidUtf8_extract_iff _ _ h₁ (by simp [le_iff])] at h₂
  obtain (rfl|h₂) := h₂
  · simp
  · exact h₂.1

/--
A `ValidPos s` is a byte offset in `s` together with a proof that this position is at a UTF-8
character boundary.
-/
@[ext]
structure ValidPos (s : String) where
  /-- The underlying byte offset of the `ValidPos`. -/
  offset : Pos
  /-- The proof that `offset` is valid for the string `s`. -/
  isValid : offset.IsValid s

-- https://github.com/leanprover/lean4/issues/10513
@[expose] section

deriving instance DecidableEq for ValidPos

end

/-- The start position of `s`, as an `s.ValidPos`. -/
@[expose]
def startValidPos (s : String) : s.ValidPos where
  offset := 0
  isValid := by simp

instance {s : String} : Inhabited s.ValidPos where
  default := s.startValidPos

@[simp]
theorem offset_startValidPos {s : String} : s.startValidPos.offset = 0 := (rfl)

/-- The past-the-end position of `s`, as an `s.ValidPos`. -/
@[expose]
def endValidPos (s : String) : s.ValidPos where
  offset := s.endPos
  isValid := by simp

theorem ValidPos.isValidUtf8_extract {s : String} (pos₁ pos₂ : s.ValidPos) :
    (s.bytes.extract pos₁.offset.byteIdx pos₂.offset.byteIdx).IsValidUtf8 := by
  by_cases h : pos₁.offset ≤ pos₂.offset
  · exact (Pos.isValidUtf8_extract_iff _ _   h pos₂.isValid.le_endPos).2 (Or.inr ⟨pos₁.isValid, pos₂.isValid⟩)
  · rw [ByteArray.extract_eq_empty_iff.2]
    · exact ByteArray.isValidUtf8_empty
    · rw [Nat.min_eq_left]
      · rw [Pos.le_iff] at h
        omega
      · have := Pos.le_iff.1 pos₂.isValid.le_endPos
        rwa [size_bytes, ← byteIdx_endPos]

/--
A region or slice of some underlying string.

A substring contains an string together with the start and end byte positions of a region of
interest. Actually extracting a substring requires copying and memory allocation, while many
substrings of the same underlying string may exist with very little overhead, and they are more
convenient than tracking the bounds by hand.

`String.Slice` bundles proofs to ensure that the start and end positions always delineate a valid
string. For this reason, it should be preferred over `Substring`.
-/
structure Slice where
  /-- The underlying strings. -/
  str : String
  /-- The byte position of the start of the string slice. -/
  startInclusive : str.ValidPos
  /-- The byte position of the end of the string slice. -/
  endExclusive : str.ValidPos
  /-- The slice is not degenerate (but it may be empty). -/
  startInclusive_le_endExclusive : startInclusive.offset ≤ endExclusive.offset

instance : Inhabited Slice where
  default := ⟨"", "".startValidPos, "".startValidPos, by simp [Pos.le_iff]⟩

@[inline, expose] -- expose for the defeq `s.toSlice.str = s`.
def toSlice (s : String) : Slice where
  str := s
  startInclusive := s.startValidPos
  endExclusive := s.endValidPos
  startInclusive_le_endExclusive := by simp [Pos.le_iff]

/-- The number of bytes of the UTF-8 encoding of the string slice. -/
@[expose]
def Slice.utf8ByteSize (s : Slice) : Pos :=
  s.endExclusive.offset - s.startInclusive.offset

@[simp]
theorem Slice.byteIdx_utf8ByteSize {s : Slice} :
    s.utf8ByteSize.byteIdx = s.endExclusive.offset.byteIdx - s.startInclusive.offset.byteIdx := (rfl)

/-- Criterion for validity of positions in string slices. -/
structure Pos.IsValidForSlice (s : Slice) (p : Pos) : Prop where
  le_utf8ByteSize : p ≤ s.utf8ByteSize
  isValid_add : (s.startInclusive.offset + p).IsValid s.str

/--
Accesses the indicated byte in the UTF-8 encoding of a string slice.

At runtime, this function is implemented by efficient, constant-time code.
-/
@[expose]
def Slice.getUtf8Byte (s : Slice) (p : Pos) (h : p < s.utf8ByteSize) : UInt8 :=
  s.str.getUtf8Byte (s.startInclusive.offset + p) (by
    have := s.endExclusive.isValid.le_endPos
    simp only [Pos.lt_iff, byteIdx_utf8ByteSize, Pos.le_iff, byteIdx_endPos, Pos.byteIdx_add] at *
    omega)

/--
Accesses the indicated byte in the UTF-8 encoding of the string slice, or panics if the position
is out-of-bounds.
-/
@[expose]
def Slice.getUtf8Byte! (s : Slice) (p : String.Pos) : UInt8 :=
  if h : p < s.utf8ByteSize then
    s.getUtf8Byte p h
  else
    panic! "String slice access is out of bounds."

@[extern "lean_string_utf8_extract"]
def ValidPos.extract {s : @& String} (b e : @& s.ValidPos) : String where
  bytes := s.bytes.extract b.offset.byteIdx e.offset.byteIdx
  isValidUtf8 := b.isValidUtf8_extract e

/-- Creates a `String` from a `String.Slice` by copying the bytes. -/
def Slice.copy (s : Slice) : String :=
  s.startInclusive.extract s.endExclusive

theorem Slice.bytes_copy {s : Slice} :
    s.copy.bytes = s.str.bytes.extract s.startInclusive.offset.byteIdx s.endExclusive.offset.byteIdx := (rfl)

@[simp]
theorem Slice.utf8ByteSize_copy {s : Slice} :
    s.copy.utf8ByteSize = s.endExclusive.offset.byteIdx - s.startInclusive.offset.byteIdx:= by
  simp [← size_bytes, bytes_copy]
  rw [Nat.min_eq_left (by simpa [Pos.le_iff] using s.endExclusive.isValid.le_endPos)]

@[simp]
theorem Slice.endPos_copy {s : Slice} : s.copy.endPos = s.utf8ByteSize := by
  simp [Pos.ext_iff]

theorem Slice.getUtf8Byte_eq_getUtf8Byte_copy {s : Slice} {p : Pos} {h : p < s.utf8ByteSize} :
    s.getUtf8Byte p h = s.copy.getUtf8Byte p (by simpa) := by
  simp [getUtf8Byte, String.getUtf8Byte, bytes_copy, ByteArray.getElem_extract]

theorem Slice.getUtf8Byte_copy {s : Slice} {p : Pos} {h} :
    s.copy.getUtf8Byte p h = s.getUtf8Byte p (by simpa using h) := by
  rw [getUtf8Byte_eq_getUtf8Byte_copy]

theorem Slice.isUtf8FirstByte_utf8ByteAt_zero {s : Slice} {h} :
    (s.getUtf8Byte 0 h).IsUtf8FirstByte := by
  simpa [getUtf8Byte_eq_getUtf8Byte_copy] using s.copy.isUtf8FirstByte_getUtf8Byte_zero

@[simp]
theorem Pos.add_zero {p : Pos} : p + 0 = p := by
  simp [Pos.ext_iff]

@[simp]
theorem Pos.isValid_copy_iff {s : Slice} {p : Pos} :
    p.IsValid s.copy ↔ p.IsValidForSlice s := by
  refine ⟨fun ⟨h₁, h₂⟩ => ⟨?_, ?_⟩, fun ⟨h₁, h₂⟩ => ⟨?_, ?_⟩⟩
  · simpa using h₁
  · have := s.startInclusive_le_endExclusive
    simp_all only [Slice.endPos_copy, le_iff, Slice.byteIdx_utf8ByteSize]
    rw [Slice.bytes_copy, ByteArray.extract_extract, Nat.add_zero, Nat.min_eq_left (by omega)] at h₂
    rw [← byteIdx_add, Pos.isValidUtf8_extract_iff] at h₂
    · rcases h₂ with (h₂|⟨-, h₂⟩)
      · rw [← h₂]
        exact s.startInclusive.isValid
      · exact h₂
    · simp [le_iff]
    · have := s.endExclusive.isValid.le_endPos
      simp_all [le_iff]
      omega
  · simpa using h₁
  · have := s.startInclusive_le_endExclusive
    simp_all only [le_iff, Slice.byteIdx_utf8ByteSize]
    rw [Slice.bytes_copy, ByteArray.extract_extract, Nat.add_zero, Nat.min_eq_left (by omega)]
    rw [← byteIdx_add, Pos.isValidUtf8_extract_iff]
    · exact Or.inr ⟨s.startInclusive.isValid, h₂⟩
    · simp [le_iff]
    · have := s.endExclusive.isValid.le_endPos
      simp_all [le_iff]
      omega

/--
A `Slice.Pos s` is a byte offset in `s` together with a proof that this position is at a UTF-8
character boundary.
-/
@[ext]
structure Slice.Pos (s : Slice) where
  /-- The underlying byte offset of the `Slice.Pos`. -/
  offset : String.Pos
  /-- The proof that `offset` is valid for the string slice `s`. -/
  isValidForSlice : offset.IsValidForSlice s

-- https://github.com/leanprover/lean4/issues/10513
@[expose] section

deriving instance DecidableEq for Slice.Pos

end

/-- The start position of `s`, as an `s.Pos`. -/
@[expose]
def Slice.startPos (s : Slice) : s.Pos where
  offset := 0
  isValidForSlice := ⟨by simp [Pos.le_iff], by simpa using s.startInclusive.isValid⟩

@[simp]
theorem ByteString.Slice.offset_startPos {s : Slice} : s.startPos.offset = 0 := (rfl)

instance {s : Slice} : Inhabited s.Pos where
  default := s.startPos

@[simp]
theorem Slice.offset_startInclusive_add_utf8ByteSize {s : Slice} :
    s.startInclusive.offset + s.utf8ByteSize = s.endExclusive.offset := by
  have := s.startInclusive_le_endExclusive
  simp_all [String.Pos.ext_iff, Pos.le_iff]

/-- The past-the-end position of `s`, as an `s.Pos`. -/
@[expose]
def Slice.endPos (s : Slice) : s.Pos where
  offset := s.utf8ByteSize
  isValidForSlice := ⟨by simp [Pos.le_iff], by simpa using s.endExclusive.isValid⟩

@[simp]
theorem ByteString.Slice.offset_endPos {s : Slice} : s.endPos.offset = s.utf8ByteSize := (rfl)

theorem Pos.isValidForSlice_iff_isUtf8FirstByte {s : Slice} {p : Pos} :
    p.IsValidForSlice s ↔ (p = s.utf8ByteSize ∨ (∃ (h : p < s.utf8ByteSize), (s.getUtf8Byte p h).IsUtf8FirstByte)) := by
  simp [← isValid_copy_iff, isValid_iff_isUtf8FirstByte, Slice.getUtf8Byte_copy]

/-- Efficiently checks whether a position is at a UTF-8 character boundary of the slice `s`. -/
@[expose]
def Pos.isValidForSlice (s : Slice) (p : Pos) : Bool :=
  if h : p < s.utf8ByteSize then
    (s.getUtf8Byte p h).IsUtf8FirstByte
  else
    p = s.utf8ByteSize

@[simp]
theorem Pos.isValidForSlice_eq_true_iff {s : Slice} {p : Pos} :
    p.isValidForSlice s = true ↔ p.IsValidForSlice s := by
  rw [isValidForSlice_iff_isUtf8FirstByte]
  fun_cases isValidForSlice with
  | case1 h =>
    simp_all only [decide_eq_true_eq, exists_true_left, iff_or_self]
    rintro rfl
    simp [lt_iff] at h
  | case2 => simp_all

@[simp]
theorem Pos.isValidForSlice_eq_false_iff {s : Slice} {p : Pos} :
    p.isValidForSlice s = false ↔ ¬ p.IsValidForSlice s := by
  rw [← Bool.not_eq_true, isValidForSlice_eq_true_iff]

instance {s : Slice} {p : Pos} : Decidable (p.IsValidForSlice s) :=
  decidable_of_iff _ Pos.isValidForSlice_eq_true_iff

theorem Pos.isValidForSlice_iff_isSome_utf8DecodeChar?_copy {s : Slice} {p : Pos} :
    p.IsValidForSlice s ↔ p = s.utf8ByteSize ∨ (s.copy.bytes.utf8DecodeChar? p.byteIdx).isSome := by
  rw [← isValid_copy_iff, isValid_iff_isSome_utf8DecodeChar?, Slice.endPos_copy]

theorem Slice.bytes_str_eq {s : Slice} :
    s.str.bytes = s.str.bytes.extract 0 s.startInclusive.offset.byteIdx ++
      s.copy.bytes ++ s.str.bytes.extract s.endExclusive.offset.byteIdx s.str.bytes.size := by
  rw [bytes_copy, ← ByteArray.extract_eq_extract_append_extract, ← ByteArray.extract_eq_extract_append_extract,
    ByteArray.extract_zero_size]
  · simp
  · simpa [Pos.le_iff] using s.endExclusive.isValid.le_endPos
  · simp
  · simpa [Pos.le_iff] using s.startInclusive_le_endExclusive

theorem Pos.isValidForSlice_iff_isSome_utf8DecodeChar? {s : Slice} {p : Pos} :
    p.IsValidForSlice s ↔ p = s.utf8ByteSize ∨ (p < s.utf8ByteSize ∧ (s.str.bytes.utf8DecodeChar? (s.startInclusive.offset.byteIdx + p.byteIdx)).isSome) := by
  refine ⟨?_, ?_⟩
  · rw [isValidForSlice_iff_isSome_utf8DecodeChar?_copy]
    rintro (rfl|h)
    · simp
    · refine Or.inr ⟨?_, ?_⟩
      · have := ByteArray.lt_size_of_isSome_utf8DecodeChar? h
        simpa [Pos.lt_iff] using this
      · rw [ByteArray.utf8DecodeChar?_eq_utf8DecodeChar?_extract] at h
        rw [Slice.bytes_str_eq, ByteArray.append_assoc, ByteArray.utf8DecodeChar?_eq_utf8DecodeChar?_extract]
        simp only [ByteArray.size_append, ByteArray.size_extract, Nat.sub_zero, Nat.le_refl,
          Nat.min_eq_left]
        have h' : s.startInclusive.offset.byteIdx ≤ s.str.bytes.size := by
          simpa [le_iff] using s.startInclusive.isValid.le_endPos
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
  · rw [isValidForSlice_iff_isUtf8FirstByte]
    rintro (rfl|⟨h₁, h₂⟩)
    · simp
    · exact Or.inr ⟨h₁, ByteArray.isUtf8FirstByte_of_isSome_utf8DecodeChar? h₂⟩

/-- Returns the byte at a position in a slice that is not the end position. -/
@[expose]
def Slice.Pos.byte {s : Slice} (pos : s.Pos) (h : pos ≠ s.endPos) : UInt8 :=
  s.getUtf8Byte pos.offset (by
    have := pos.isValidForSlice.le_utf8ByteSize
    simp_all [Pos.ext_iff, String.Pos.ext_iff, Pos.le_iff, Pos.lt_iff]
    omega)

theorem Slice.Pos.isUtf8FirstByte_byte {s : Slice} {pos : s.Pos} {h : pos ≠ s.endPos} :
    (pos.byte h).IsUtf8FirstByte :=
  ((Pos.isValidForSlice_iff_isUtf8FirstByte.1 pos.isValidForSlice).elim (fun h' => (h (Pos.ext h')).elim) (·.2))

/-- Given a valid position on a slice `s`, obtains the corresponding valid position on the
underlying string `s.str`. -/
def Slice.Pos.str {s : Slice} (pos : s.Pos) : s.str.ValidPos where
  offset := s.startInclusive.offset + pos.offset
  isValid := pos.isValidForSlice.isValid_add

@[simp]
theorem Slice.Pos.offset_str {s : Slice} {pos : s.Pos} :
    pos.str.offset = s.startInclusive.offset + pos.offset := (rfl)

@[simp]
theorem Slice.Pos.offset_str_le_offset_endExclusive {s : Slice} {pos : s.Pos} :
    pos.str.offset ≤ s.endExclusive.offset := by
  have := pos.isValidForSlice.le_utf8ByteSize
  have := s.startInclusive_le_endExclusive
  simp only [Pos.le_iff, byteIdx_utf8ByteSize, offset_str, Pos.byteIdx_add, ge_iff_le] at *
  omega

theorem Slice.Pos.offset_le_offset_str {s : Slice} {pos : s.Pos} :
    pos.offset ≤ pos.str.offset := by
  simp [String.Pos.le_iff]

@[simp]
theorem Slice.Pos.offset_le_offset_endExclusive {s : Slice} {pos : s.Pos} :
    pos.offset ≤ s.endExclusive.offset :=
  Pos.le_trans offset_le_offset_str offset_str_le_offset_endExclusive

/-- Given a slice and a valid position within the slice, obtain a new slice on the same underlying
string by replacing the start of the slice with the given position. -/
@[expose] -- for the defeq `(s.replaceStart pos).str = s.str`
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
@[expose] -- for the defeq `(s.replaceEnd pos).str = s.str`
def Slice.replaceEnd (s : Slice) (pos : s.Pos) : Slice where
  str := s.str
  startInclusive := s.startInclusive
  endExclusive := pos.str
  startInclusive_le_endExclusive := by simp [String.Pos.le_iff]

@[simp]
theorem Slice.str_replaceEnd {s : Slice} {pos : s.Pos} :
    (s.replaceEnd pos).str = s.str := rfl

@[simp]
theorem Slice.startInclusive_replaceEnd {s : Slice} {pos : s.Pos} :
    (s.replaceEnd pos).startInclusive = s.startInclusive := rfl

@[simp]
theorem Slice.endExclusive_replaceEnd {s : Slice} {pos : s.Pos} :
    (s.replaceEnd pos).endExclusive = pos.str := rfl

@[simp]
theorem Slice.utf8ByteSize_replaceStart {s : Slice} {pos : s.Pos} :
    (s.replaceStart pos).utf8ByteSize = s.utf8ByteSize - pos.offset := by
  ext
  simp
  omega

@[simp]
theorem Slice.utf8ByteSize_replaceEnd {s : Slice} {pos : s.Pos} :
    (s.replaceEnd pos).utf8ByteSize = pos.offset := by
  ext
  simp

theorem Pos.add_comm (a b : Pos) : a + b = b + a := by
  ext
  simpa using Nat.add_comm _ _

theorem Pos.add_assoc (a b c : Pos) : a + b + c = a + (b + c) := by
  ext
  simpa using Nat.add_assoc _ _ _

theorem Pos.isValidForSlice_replaceStart {s : Slice} {p : s.Pos} {off : Pos} :
    off.IsValidForSlice (s.replaceStart p) ↔ (p.offset + off).IsValidForSlice s := by
  refine ⟨fun ⟨h₁, h₂⟩ => ⟨?_, ?_⟩, fun ⟨h₁, h₂⟩ => ⟨?_, ?_⟩⟩
  · have := p.isValidForSlice.le_utf8ByteSize
    simp_all [le_iff]
    omega
  · simp only [Slice.str_replaceStart, Slice.startInclusive_replaceStart, Slice.Pos.offset_str] at h₂
    rwa [← Pos.add_assoc]
  · simp_all [Pos.le_iff]
    omega
  · simp only [Slice.str_replaceStart, Slice.startInclusive_replaceStart, Slice.Pos.offset_str]
    rwa [Pos.add_assoc]

theorem Pos.isValidForSlice_replaceEnd {s : Slice} {p : s.Pos} {off : Pos} :
    off.IsValidForSlice (s.replaceEnd p) ↔ off ≤ p.offset ∧ off.IsValidForSlice s := by
  refine ⟨fun ⟨h₁, h₂⟩ => ⟨?_, ?_, ?_⟩, fun ⟨h₁, ⟨h₂, h₃⟩⟩ => ⟨?_, ?_⟩⟩
  · simpa using h₁
  · simp only [Slice.utf8ByteSize_replaceEnd] at h₁
    exact Pos.le_trans h₁ p.isValidForSlice.le_utf8ByteSize
  · simpa using h₂
  · simpa using h₁
  · simpa using h₃

@[extern "lean_string_utf8_get", expose]
def decodeChar (s : @& String) (byteIdx : @& Nat) (h : (s.bytes.utf8DecodeChar? byteIdx).isSome) : Char :=
  s.bytes.utf8DecodeChar byteIdx h

/-- Obtains the character at the given position in the string. -/
@[expose]
def Slice.Pos.get {s : Slice} (pos : s.Pos) (h : pos ≠ s.endPos) : Char :=
  s.str.decodeChar (s.startInclusive.offset.byteIdx + pos.offset.byteIdx)
    ((Pos.isValidForSlice_iff_isSome_utf8DecodeChar?.1 pos.isValidForSlice).elim (by simp_all [Pos.ext_iff]) (·.2))

theorem Slice.Pos.get_eq_utf8DecodeChar {s : Slice} (pos : s.Pos) (h : pos ≠ s.endPos) :
    pos.get h = s.str.bytes.utf8DecodeChar (s.startInclusive.offset.byteIdx + pos.offset.byteIdx)
      ((Pos.isValidForSlice_iff_isSome_utf8DecodeChar?.1 pos.isValidForSlice).elim (by simp_all [Pos.ext_iff]) (·.2)) := (rfl)

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
theorem offset_endValidPos {s : String} : s.endValidPos.offset = s.endPos := (rfl)

@[simp]
theorem copy_toSlice {s : String} : s.toSlice.copy = s := by
  simp [← bytes_inj, Slice.bytes_copy, ← size_bytes]

@[simp]
theorem Pos.isValidForSlice_toSlice_iff {s : String} {p : Pos} :
    p.IsValidForSlice s.toSlice ↔ p.IsValid s := by
  rw [← isValid_copy_iff, copy_toSlice]

theorem Pos.IsValid.toSlice {s : String} {p : Pos} (h : p.IsValid s) :
    p.IsValidForSlice s.toSlice :=
  isValidForSlice_toSlice_iff.2 h

theorem Pos.IsValidForSlice.ofSlice {s : String} {p : Pos} (h : p.IsValidForSlice s.toSlice) :
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
theorem Slice.Pos.ofset_ofSlice {s : String} {pos : s.toSlice.Pos} : pos.ofSlice.offset = pos.offset := (rfl)

@[simp]
theorem utf8ByteSize_toSlice {s : String} : s.toSlice.utf8ByteSize = s.endPos := by
  rw [← Slice.endPos_copy, copy_toSlice]

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

/--
Returns the character at the position `pos` of a string, taking a proof that `p` is not the
past-the-end position.

This function is overridden with an efficient implementation in runtime code.

Examples: TODO!!
* `"abc".get ⟨1⟩ = 'b'`
* `"abc".get ⟨3⟩ = (default : Char)` because byte `3` is at the end of the string.
* `"L∃∀N".get ⟨2⟩ = (default : Char)` because byte `2` is in the middle of `'∃'`.
-/
@[expose]
def ValidPos.get {s : String} (pos : s.ValidPos) (h : pos ≠ s.endValidPos) : Char :=
  pos.toSlice.get (ne_of_apply_ne Slice.Pos.ofSlice (by simp [h]))

/--
Returns the character at the position `pos` of a string, or `none` if the position is the
past-the-end position.

This function is overridden with an efficient implementation in runtime code.
-/
@[expose]
def ValidPos.get? {s : String} (pos : s.ValidPos) : Option Char :=
  pos.toSlice.get?

/--
Returns the character at the position `pos` of a string, or panics if the position is the
past-the-end position.

This function is overridden with an efficient implementation in runtime code.
-/
@[expose]
def ValidPos.get! {s : String} (pos : s.ValidPos) : Char :=
  pos.toSlice.get!

/--
Returns the byte at the position `pos` of a string.
-/
def ValidPos.byte {s : String} (pos : s.ValidPos) (h : pos ≠ s.endValidPos) : UInt8 :=
  pos.toSlice.byte (ne_of_apply_ne Slice.Pos.ofSlice (by simp [h]))

@[simp]
theorem append_left_inj {s₁ s₂ : String} (t : String) :
    s₁ ++ t = s₂ ++ t ↔ s₁ = s₂ := by
  simp [← String.data_inj]

theorem append_assoc {s₁ s₂ s₃ : String} : s₁ ++ s₂ ++ s₃ = s₁ ++ (s₂ ++ s₃) := by
  simp [← String.data_inj]

@[simp]
theorem utf8ByteSize_eq_zero_iff {s : String} : s.utf8ByteSize = 0 ↔ s = "" := by
  refine ⟨fun h => ?_, fun h => h ▸ utf8ByteSize_empty⟩
  simpa [← bytes_inj, ← ByteArray.size_eq_zero_iff] using h

@[simp]
theorem Pos.eq_zero_iff {p : Pos} : p = 0 ↔ p.byteIdx = 0 :=
  Pos.ext_iff

theorem endPos_eq_zero_iff {b : String} : b.endPos = 0 ↔ b = "" := by
  simp

@[simp]
theorem startValidPos_eq_endValidPos_iff {b : String} : b.startValidPos = b.endValidPos ↔ b = "" := by
  simp [← utf8ByteSize_eq_zero_iff, ValidPos.ext_iff, Eq.comm (b := b.endPos)]

@[simp]
theorem data_eq_nil_iff {b : String} : b.data = [] ↔ b = "" := by
  rw [← List.asString_inj, asString_data, List.asString_nil]

@[simp]
theorem _root_.List.asString_eq_empty_iff {l : List Char} : l.asString = "" ↔ l = [] := by
  rw [← data_inj, List.data_asString, data_empty]

@[simp]
theorem _root_.List.length_asString {l : List Char} : l.asString.length = l.length := by
  rw [← String.length_data, List.data_asString]

theorem isSome_utf8DecodeChar?_zero {b : String} (hb : b ≠ "") : (b.bytes.utf8DecodeChar? 0).isSome := by
  refine (((Pos.isValid_iff_isSome_utf8DecodeChar? (s := b)).1 Pos.isValid_zero).elim ?_ id)
  rw [eq_comm, endPos_eq_zero_iff]
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
  simp only [str_replaceEnd, startInclusive_replaceEnd, endExclusive_replaceEnd,
    Slice.Pos.offset_str, Pos.byteIdx_add, str_replaceStart, startInclusive_replaceStart,
    endExclusive_replaceStart, ByteArray.extract_append_extract, Nat.le_add_right, Nat.min_eq_left]
  rw [Nat.max_eq_right]
  exact pos.offset_str_le_offset_endExclusive

/-- Given a slice `s` and a position on `s.copy`, obtain the corresponding position on `s`. -/
def ValidPos.ofCopy {s : Slice} (pos : s.copy.ValidPos) : s.Pos where
  offset := pos.offset
  isValidForSlice := Pos.isValid_copy_iff.1 pos.isValid

@[simp]
theorem ValidPos.offset_ofCopy {s : Slice} {pos : s.copy.ValidPos} : pos.ofCopy.offset = pos.offset := (rfl)

/-- Given a slice `s` and a position on `s`, obtain the corresponding position on `s.copy.` -/
def Slice.Pos.toCopy {s : Slice} (pos : s.Pos) : s.copy.ValidPos where
  offset := pos.offset
  isValid := Pos.isValid_copy_iff.2 pos.isValidForSlice

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
    ByteString.Slice.offset_startPos, Pos.byteIdx_zero, ValidPos.offset_toSlice, Nat.zero_add]
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
  simp [getUtf8Byte, String.getUtf8Byte, bytes_copy, ByteArray.getElem_extract]

theorem Slice.Pos.byte_eq_byte_toCopy {s : Slice} {pos : s.Pos} {h} :
    pos.byte h = pos.toCopy.byte (ne_of_apply_ne ValidPos.ofCopy (by simp [h])) :=
  (byte_toCopy _).symm

/-- Given a position in `s.replaceStart p₀`, obtain the corresponding position in `s`. -/
def Slice.Pos.ofReplaceStart {s : Slice} {p₀ : s.Pos} (pos : (s.replaceStart p₀).Pos) : s.Pos where
  offset := p₀.offset + pos.offset
  isValidForSlice := Pos.isValidForSlice_replaceStart.1 pos.isValidForSlice

@[simp]
theorem Slice.Pos.offset_ofReplaceStart {s : Slice} {p₀ : s.Pos} {pos : (s.replaceStart p₀).Pos} :
    (ofReplaceStart pos).offset = p₀.offset + pos.offset := (rfl)

/-- Given a position in `s` that is at least `p₀`, obtain the corresponding position in
`s.replaceStart p₀`. -/
def Slice.Pos.toReplaceStart {s : Slice} (p₀ : s.Pos) (pos : s.Pos) (h : p₀.offset ≤ pos.offset) :
    (s.replaceStart p₀).Pos where
  offset := pos.offset - p₀.offset
  isValidForSlice := Pos.isValidForSlice_replaceStart.2 (by
    have : p₀.offset + (pos.offset - p₀.offset) = pos.offset := by
      simp_all [Pos.le_iff, String.Pos.ext_iff]
    simpa [this] using pos.isValidForSlice)

@[simp]
theorem Slice.Pos.offset_toReplaceStart {s : Slice} {p₀ : s.Pos} {pos : s.Pos} {h} :
    (toReplaceStart p₀ pos h).offset = pos.offset - p₀.offset := (rfl)

@[simp]
theorem Slice.Pos.ofReplaceStart_startPos {s : Slice} {pos : s.Pos} :
    ofReplaceStart (s.replaceStart pos).startPos = pos :=
  Slice.Pos.ext (by simp)

@[simp]
theorem Slice.Pos.ofReplaceStart_endPos {s : Slice} {pos : s.Pos} :
    ofReplaceStart (s.replaceStart pos).endPos = s.endPos := by
  have := pos.isValidForSlice.le_utf8ByteSize
  simp_all [Pos.ext_iff, String.Pos.ext_iff, Pos.le_iff]

theorem Slice.Pos.ofReplaceStart_inj {s : Slice} {p₀ : s.Pos} {pos pos' : (s.replaceStart p₀).Pos} :
    ofReplaceStart pos = ofReplaceStart pos' ↔ pos = pos' := by
  simp [Pos.ext_iff, String.Pos.ext_iff]

theorem Slice.Pos.get_eq_get_ofReplaceStart {s : Slice} {p₀ : s.Pos} {pos : (s.replaceStart p₀).Pos} {h} :
    pos.get h = (ofReplaceStart pos).get (by rwa [← ofReplaceStart_endPos, ne_eq, ofReplaceStart_inj]) := by
  simp [Slice.Pos.get, Nat.add_assoc]

theorem Slice.Pos.copy_eq_append_get {s : Slice} {pos : s.Pos} (h : pos ≠ s.endPos) :
    ∃ t₁ t₂ : String, s.copy = t₁ ++ singleton (pos.get h) ++ t₂ ∧ t₁.utf8ByteSize = pos.offset.byteIdx := by
  obtain ⟨t₂, ht₂⟩ := (s.replaceStart pos).copy.eq_singleton_append (by simpa [← ValidPos.ofCopy_inj, ← ofReplaceStart_inj])
  refine ⟨(s.replaceEnd pos).copy, t₂, ?_, by simp⟩
  simp only [Slice.startValidPos_copy, get_toCopy, get_eq_get_ofReplaceStart, ofReplaceStart_startPos] at ht₂
  rw [append_assoc, ← ht₂, ← copy_eq_copy_replaceEnd]

theorem Slice.Pos.utf8ByteSize_byte {s : Slice} {pos : s.Pos} {h : pos ≠ s.endPos} :
    (pos.byte h).utf8ByteSize pos.isUtf8FirstByte_byte = ⟨(pos.get h).utf8Size⟩ := by
  simp [getUtf8Byte, byte, String.getUtf8Byte, get_eq_utf8DecodeChar, ByteArray.utf8Size_utf8DecodeChar]

/-- Advances a valid position on a slice to the next valid position, given a proof that the
position is not the past-the-end position, which guarantees that such a position exists. -/
@[expose]
def Slice.Pos.next {s : Slice} (pos : s.Pos) (h : pos ≠ s.endPos) : s.Pos where
  offset := pos.offset + (pos.byte h).utf8ByteSize pos.isUtf8FirstByte_byte
  isValidForSlice := by
    obtain ⟨t₁, t₂, ht, ht'⟩ := copy_eq_append_get h
    replace ht' : pos.offset = ⟨t₁.utf8ByteSize⟩ := Eq.symm (String.Pos.ext ht')
    rw [utf8ByteSize_byte, ← Pos.isValid_copy_iff, ht, ht']
    refine Pos.IsValid.append_right ?_ t₂
    refine Pos.IsValid.append_left ?_ t₁
    exact Pos.isValid_singleton.2 (Or.inr rfl)

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
theorem Slice.Pos.byteIdx_offset_next {s : Slice} {pos : s.Pos} {h : pos ≠ s.endPos} :
    (pos.next h).offset.byteIdx = pos.offset.byteIdx + (pos.get h).utf8Size := by
  simp [next, utf8ByteSize_byte]

/-- Increases the byte offset of the position by `1`. Not to be confused with `ValidPos.next`. -/
@[expose]
def Pos.inc (p : Pos) : Pos :=
  ⟨p.byteIdx + 1⟩

@[simp]
theorem Pos.byteIdx_inc {p : Pos} : p.inc.byteIdx = p.byteIdx + 1 := (rfl)

/-- Decreases the byte offset of the position by `1`. Not to be confused with `ValidPos.prev`. -/
@[expose]
def Pos.dec (p : Pos) : Pos :=
  ⟨p.byteIdx - 1⟩

@[simp]
theorem Pos.byteIdx_dec {p : Pos} : p.dec.byteIdx = p.byteIdx - 1 := (rfl)

@[expose]
def Slice.Pos.prevAux {s : Slice} (pos : s.Pos) (h : pos ≠ s.startPos) : String.Pos :=
  go (pos.offset.byteIdx - 1) (by
    have := pos.isValidForSlice.le_utf8ByteSize
    simp [Pos.le_iff, Pos.lt_iff, Pos.ext_iff] at ⊢ this h
    omega)
where
  go (off : Nat) (h₁ : ⟨off⟩ < s.utf8ByteSize) : String.Pos :=
    if hbyte : (s.getUtf8Byte ⟨off⟩ h₁).IsUtf8FirstByte then
      ⟨off⟩
    else
      have : 0 ≠ off := by
        intro h
        obtain hoff : (⟨off⟩ : String.Pos) = 0 := by simpa [String.Pos.ext_iff] using h.symm
        simp [hoff, s.isUtf8FirstByte_utf8ByteAt_zero] at hbyte
      match off with
      | 0 => False.elim (by contradiction)
      | off + 1 => go off (by simp [Pos.lt_iff] at ⊢ h₁; omega)
  termination_by structural off

theorem Pos.isValidForSlice_prevAuxGo {s : Slice} (off : Nat) (h₁ : ⟨off⟩ < s.utf8ByteSize) :
    (Slice.Pos.prevAux.go off h₁).IsValidForSlice s := by
  induction off with
  | zero =>
    rw [Slice.Pos.prevAux.go]
    split
    · exact Pos.isValidForSlice_iff_isUtf8FirstByte.2 (Or.inr ⟨_, ‹_›⟩)
    · simpa using elim
  | succ off ih =>
    rw [Slice.Pos.prevAux.go]
    split
    · exact Pos.isValidForSlice_iff_isUtf8FirstByte.2 (Or.inr ⟨_, ‹_›⟩)
    · simpa using ih _
where
  elim {P : Pos → Prop} {h : False} : P h.elim := h.elim

theorem Pos.isValidForSlice_prevAux {s : Slice} (pos : s.Pos) (h : pos ≠ s.startPos) :
    (pos.prevAux h).IsValidForSlice s :=
  isValidForSlice_prevAuxGo ..

/-- Returns the previous valid position before the given position, given a proof that the position
is not the start position, which guarantees that such a position exists. -/
@[expose]
def Slice.Pos.prev {s : Slice} (pos : s.Pos) (h : pos ≠ s.startPos) : s.Pos where
  offset := prevAux pos h
  isValidForSlice := Pos.isValidForSlice_prevAux _ _

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
@[expose]
def Slice.pos (s : Slice) (off : String.Pos) (h : off.IsValidForSlice s) : s.Pos where
  offset := off
  isValidForSlice := h

/-- Constructs a valid position on `s` from a position, returning `none` if the position is not valid. -/
@[expose]
def Slice.pos? (s : Slice) (off : String.Pos) : Option s.Pos :=
  if h : off.isValidForSlice s then
    some (s.pos off (Pos.isValidForSlice_eq_true_iff.1 h))
  else
    none

/-- Constructs a valid position `s` from a position, panicking if the position is not valid. -/
@[expose]
def Slice.pos! (s : Slice) (off : String.Pos) : s.Pos :=
  if h : off.isValidForSlice s then
    s.pos off (Pos.isValidForSlice_eq_true_iff.1 h)
  else
    panic! "Offset is not at a valid UTF-8 character boundary"

/-- Advances a valid position on a string to the next valid position, given a proof that the
position is not the past-the-end position, which guarantees that such a position exists. -/
@[expose]
def ValidPos.next {s : String} (pos : s.ValidPos) (h : pos ≠ s.endValidPos) : s.ValidPos :=
  (pos.toSlice.next (ne_of_apply_ne Slice.Pos.ofSlice (by simpa))).ofSlice

/-- Advances a valid position on a string to the next valid position, or returns `none` if the
given position is the past-the-end position. -/
@[expose]
def ValidPos.next? {s : String} (pos : s.ValidPos) : Option s.ValidPos :=
  pos.toSlice.next?.map Slice.Pos.ofSlice

/-- Advances a valid position on a string to the next valid position, or panics if the given
position is the past-the-end position. -/
@[expose]
def ValidPos.next! {s : String} (pos : s.ValidPos) : s.ValidPos :=
  pos.toSlice.next!.ofSlice

/-- Returns the previous valid position before the given position, given a proof that the position
is not the start position, which guarantees that such a position exists. -/
@[expose]
def ValidPos.prev {s : String} (pos : s.ValidPos) (h : pos ≠ s.startValidPos) : s.ValidPos :=
  (pos.toSlice.prev (ne_of_apply_ne Slice.Pos.ofSlice (by simpa))).ofSlice

/-- Returns the previous valid position before the given position, or `none` if the position is
the start position. -/
@[expose]
def ValidPos.prev? {s : String} (pos : s.ValidPos) : Option s.ValidPos :=
  pos.toSlice.prev?.map Slice.Pos.ofSlice

/-- Returns the previous valid position before the given position, or panics if the position is
the start position. -/
@[expose]
def ValidPos.prev! {s : String} (pos : s.ValidPos) : s.ValidPos :=
  pos.toSlice.prev!.ofSlice

/-- Constructs a valid position on `s` from a position and a proof that it is valid. -/
@[expose]
def pos (s : String) (off : Pos) (h : off.IsValid s) : s.ValidPos :=
  (s.toSlice.pos off h.toSlice).ofSlice

/-- Constructs a valid position on `s` from a position, returning `none` if the position is not valid. -/
@[expose]
def pos? (s : String) (off : Pos) : Option s.ValidPos :=
  (s.toSlice.pos? off).map Slice.Pos.ofSlice

/-- Constructs a valid position `s` from a position, panicking if the position is not valid. -/
@[expose]
def pos! (s : String) (off : Pos) : s.ValidPos :=
  (s.toSlice.pos! off).ofSlice

/-- Constructs a valid position on `t` from a valid position on `s` and a proof that `s = t`. -/
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
def Slice.findNextPos (offset : String.Pos) (s : Slice) (_h : offset < s.utf8ByteSize) : s.Pos :=
  go offset.inc
where
  go (offset : String.Pos) : s.Pos :=
    if h : offset < s.utf8ByteSize then
      if h' : (s.getUtf8Byte offset h).IsUtf8FirstByte then
        s.pos offset (Pos.isValidForSlice_iff_isUtf8FirstByte.2 (Or.inr ⟨_, h'⟩))
      else
        go offset.inc
    else
      s.endPos
  termination_by s.utf8ByteSize.byteIdx - offset.byteIdx
  decreasing_by
    simp only [Pos.lt_iff, byteIdx_utf8ByteSize, Pos.byteIdx_inc, gt_iff_lt] at h ⊢
    omega

theorem Slice.Pos.prevAuxGo_le_self {s : Slice} {p : Nat} {h : ⟨p⟩ < s.utf8ByteSize} :
    prevAux.go p h ≤ ⟨p⟩ := by
  induction p with
  | zero =>
    rw [prevAux.go]
    split
    · simp [Pos.le_iff]
    · simpa using elim (· ≤ { })
  | succ p ih =>
    rw [prevAux.go]
    split
    · simp [Pos.le_iff]
    · simpa using Nat.le_trans ih (by simp)
where
  elim (P : String.Pos → Prop) {h : False} : P h.elim := h.elim

theorem Pos.lt_of_le_of_lt {a b c : Pos} : a ≤ b → b < c → a < c := by
  simpa [le_iff, lt_iff] using Nat.lt_of_le_of_lt

theorem Slice.Pos.prevAux_lt_self {s : Slice} {p : s.Pos} {h} : p.prevAux h < p.offset := by
  rw [prevAux]
  refine Pos.lt_of_le_of_lt prevAuxGo_le_self ?_
  simp [Pos.ext_iff, Pos.lt_iff] at *
  omega

theorem Slice.Pos.prevAux_lt_utf8ByteSize {s : Slice} {p : s.Pos} {h} : p.prevAux h < s.utf8ByteSize :=
  Pos.lt_of_lt_of_le prevAux_lt_self p.isValidForSlice.le_utf8ByteSize

theorem Pos.ne_of_lt {a b : Pos} : a < b → a ≠ b := by
  simpa [lt_iff, Pos.ext_iff] using Nat.ne_of_lt

theorem Slice.Pos.prev_ne_endPos {s : Slice} {p : s.Pos} {h} : p.prev h ≠ s.endPos := by
  simpa [Pos.ext_iff, prev] using Pos.ne_of_lt prevAux_lt_utf8ByteSize

theorem Slice.Pos.offset_prev_lt_offset {s : Slice} {p : s.Pos} {h} : (p.prev h).offset < p.offset := by
  simpa [prev] using prevAux_lt_self

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
def utf8GetAux : List Char → Pos → Pos → Char
  | [],    _, _ => default
  | c::cs, i, p => if i = p then c else utf8GetAux cs (i + c) p

/--
Returns the character at position `p` of a string. If `p` is not a valid position, returns the
fallback value `(default : Char)`, which is `'A'`, but does not panic.

This function is overridden with an efficient implementation in runtime code. See
`String.utf8GetAux` for the reference implementation.

Examples:
* `"abc".get ⟨1⟩ = 'b'`
* `"abc".get ⟨3⟩ = (default : Char)` because byte `3` is at the end of the string.
* `"L∃∀N".get ⟨2⟩ = (default : Char)` because byte `2` is in the middle of `'∃'`.
-/
@[extern "lean_string_utf8_get", expose]
def get (s : @& String) (p : @& Pos) : Char :=
  utf8GetAux s.data 0 p

@[expose]
def utf8GetAux? : List Char → Pos → Pos → Option Char
  | [],    _, _ => none
  | c::cs, i, p => if i = p then some c else utf8GetAux? cs (i + c) p


/--
Returns the character at position `p` of a string. If `p` is not a valid position, returns `none`.

This function is overridden with an efficient implementation in runtime code. See
`String.utf8GetAux?` for the reference implementation.

Examples:
* `"abc".get? ⟨1⟩ = some 'b'`
* `"abc".get? ⟨3⟩ = none`
* `"L∃∀N".get? ⟨1⟩ = some '∃'`
* `"L∃∀N".get? ⟨2⟩ = none`
-/
@[extern "lean_string_utf8_get_opt", expose]
def get? : (@& String) → (@& Pos) → Option Char
  | s, p => utf8GetAux? s.data 0 p

/--
Returns the character at position `p` of a string. Panics if `p` is not a valid position.

See `String.get?` for a safer alternative.

This function is overridden with an efficient implementation in runtime code. See
`String.utf8GetAux` for the reference implementation.

Examples
* `"abc".get! ⟨1⟩ = 'b'`
-/
@[extern "lean_string_utf8_get_bang", expose]
def get! (s : @& String) (p : @& Pos) : Char :=
  match s with
  | s => utf8GetAux s.data 0 p

@[expose]
def utf8SetAux (c' : Char) : List Char → Pos → Pos → List Char
  | [],    _, _ => []
  | c::cs, i, p =>
    if i = p then (c'::cs) else c::(utf8SetAux c' cs (i + c) p)

/--
Replaces the character at a specified position in a string with a new character. If the position is
invalid, the string is returned unchanged.

If both the replacement character and the replaced character are 7-bit ASCII characters and the
string is not shared, then it is updated in-place and not copied.

Examples:
* `"abc".set ⟨1⟩ 'B' = "aBc"`
* `"abc".set ⟨3⟩ 'D' = "abc"`
* `"L∃∀N".set ⟨4⟩ 'X' = "L∃XN"`
* `"L∃∀N".set ⟨2⟩ 'X' = "L∃∀N"` because `'∃'` is a multi-byte character, so the byte index `2` is an
  invalid position.
-/
@[extern "lean_string_utf8_set", expose]
def set : String → (@& Pos) → Char → String
  | s, i, c => (utf8SetAux c s.data 0 i).asString

/--
Replaces the character at position `p` in the string `s` with the result of applying `f` to that
character. If `p` is an invalid position, the string is returned unchanged.

If both the replacement character and the replaced character are 7-bit ASCII characters and the
string is not shared, then it is updated in-place and not copied.

Examples:
* `"abc".modify ⟨1⟩ Char.toUpper = "aBc"`
* `"abc".modify ⟨3⟩ Char.toUpper = "abc"`
-/
@[expose]
def modify (s : String) (i : Pos) (f : Char → Char) : String :=
  s.set i <| f <| s.get i

/--
Returns the next position in a string after position `p`. If `p` is not a valid position or
`p = s.endPos`, returns the position one byte after `p`.

A run-time bounds check is performed to determine whether `p` is at the end of the string. If a
bounds check has already been performed, use `String.next'` to avoid a repeated check.

Some examples of edge cases:
* `"abc".next ⟨3⟩ = ⟨4⟩`, since `3 = "abc".endPos`
* `"L∃∀N".next ⟨2⟩ = ⟨3⟩`, since `2` points into the middle of a multi-byte UTF-8 character

Examples:
* `"abc".get ("abc".next 0) = 'b'`
* `"L∃∀N".get (0 |> "L∃∀N".next |> "L∃∀N".next) = '∀'`
-/
@[extern "lean_string_utf8_next", expose]
def next (s : @& String) (p : @& Pos) : Pos :=
  let c := get s p
  p + c

@[expose]
def utf8PrevAux : List Char → Pos → Pos → Pos
  | [],    _, p => ⟨p.byteIdx - 1⟩
  | c::cs, i, p =>
    let i' := i + c
    if p ≤ i' then i else utf8PrevAux cs i' p

/--
Returns the position in a string before a specified position, `p`. If `p = ⟨0⟩`, returns `0`. If `p`
is greater than `endPos`, returns the position one byte before `p`. Otherwise, if `p` occurs in the
middle of a multi-byte character, returns the beginning position of that character.

For example, `"L∃∀N".prev ⟨3⟩` is `⟨1⟩`, since byte 3 occurs in the middle of the multi-byte
character `'∃'` that starts at byte 1.

Examples:
* `"abc".get ("abc".endPos |> "abc".prev) = 'c'`
* `"L∃∀N".get ("L∃∀N".endPos |> "L∃∀N".prev |> "L∃∀N".prev |> "L∃∀N".prev) = '∃'`
-/
@[extern "lean_string_utf8_prev", expose]
def prev : (@& String) → (@& Pos) → Pos
  | s, p => utf8PrevAux s.data 0 p

/--
Returns the first character in `s`. If `s = ""`, returns `(default : Char)`.

Examples:
* `"abc".front = 'a'`
* `"".front = (default : Char)`
-/
@[inline, expose] def front (s : String) : Char :=
  get s 0

@[export lean_string_front]
def Internal.frontImpl (s : String) : Char :=
  String.front s

/--
Returns the last character in `s`. If `s = ""`, returns `(default : Char)`.

Examples:
* `"abc".back = 'c'`
* `"".back = (default : Char)`
-/
@[inline, expose] def back (s : String) : Char :=
  get s (prev s s.endPos)

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
def atEnd : (@& String) → (@& Pos) → Bool
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

Examples:
* `"abc".get' 0 (by decide) = 'a'`
* `let lean := "L∃∀N"; lean.get' (0 |> lean.next |> lean.next) (by decide) = '∀'`
-/
@[extern "lean_string_utf8_get_fast", expose]
def get' (s : @& String) (p : @& Pos) (h : ¬ s.atEnd p) : Char :=
  match s with
  | s => utf8GetAux s.data 0 p

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

Example:
* `let abc := "abc"; abc.get (abc.next' 0 (by decide)) = 'b'`
-/
@[extern "lean_string_utf8_next_fast", expose]
def next' (s : @& String) (p : @& Pos) (h : ¬ s.atEnd p) : Pos :=
  let c := get s p
  p + c

@[deprecated Char.utf8Size_pos (since := "2026-06-04")] abbrev one_le_csize := Char.utf8Size_pos

@[simp] theorem pos_lt_eq (p₁ p₂ : Pos) : (p₁ < p₂) = (p₁.1 < p₂.1) := rfl

@[simp] theorem pos_add_char (p : Pos) (c : Char) : (p + c).byteIdx = p.byteIdx + c.utf8Size := rfl

protected theorem Pos.ne_zero_of_lt : {a b : Pos} → a < b → b ≠ 0
  | _, _, hlt, rfl => Nat.not_lt_zero _ hlt

theorem lt_next (s : String) (i : Pos) : i.1 < (s.next i).1 :=
  Nat.add_lt_add_left (Char.utf8Size_pos _) _

theorem utf8PrevAux_lt_of_pos : ∀ (cs : List Char) (i p : Pos), i < p → p ≠ 0 →
    (utf8PrevAux cs i p).1 < p.1
  | [], _, _, _, h => Nat.sub_one_lt (mt (congrArg Pos.mk) h)
  | c::cs, i, p, h, h' => by
    simp [utf8PrevAux]
    apply iteInduction (motive := (Pos.byteIdx · < _)) <;> intro h''
    next => exact h
    next => exact utf8PrevAux_lt_of_pos _ _ _ (Nat.lt_of_not_le h'') h'

theorem prev_lt_of_pos (s : String) (i : Pos) (h : i ≠ 0) : (s.prev i).1 < i.1 :=
  utf8PrevAux_lt_of_pos _ _ _ (Nat.zero_lt_of_ne_zero (mt (congrArg Pos.mk) h)) h

def posOfAux (s : String) (c : Char) (stopPos : Pos) (pos : Pos) : Pos :=
  if h : pos < stopPos then
    if s.get pos == c then pos
    else
      have := Nat.sub_lt_sub_left h (lt_next s pos)
      posOfAux s c stopPos (s.next pos)
  else pos
termination_by stopPos.1 - pos.1

/--
Returns the position of the first occurrence of a character, `c`, in a string `s`. If `s` does not
contain `c`, returns `s.endPos`.

Examples:
* `"abcba".posOf 'a' = ⟨0⟩`
* `"abcba".posOf 'z' = ⟨5⟩`
* `"L∃∀N".posOf '∀' = ⟨4⟩`
-/
@[inline] def posOf (s : String) (c : Char) : Pos :=
  posOfAux s c s.endPos 0

@[export lean_string_posof]
def Internal.posOfImpl (s : String) (c : Char) : Pos :=
  String.posOf s c

def revPosOfAux (s : String) (c : Char) (pos : Pos) : Option Pos :=
  if h : pos = 0 then none
  else
    have := prev_lt_of_pos s pos h
    let pos := s.prev pos
    if s.get pos == c then some pos
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
@[inline] def revPosOf (s : String) (c : Char) : Option Pos :=
  revPosOfAux s c s.endPos

def findAux (s : String) (p : Char → Bool) (stopPos : Pos) (pos : Pos) : Pos :=
  if h : pos < stopPos then
    if p (s.get pos) then pos
    else
      have := Nat.sub_lt_sub_left h (lt_next s pos)
      findAux s p stopPos (s.next pos)
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
@[inline] def find (s : String) (p : Char → Bool) : Pos :=
  findAux s p s.endPos 0

def revFindAux (s : String) (p : Char → Bool) (pos : Pos) : Option Pos :=
  if h : pos = 0 then none
  else
    have := prev_lt_of_pos s pos h
    let pos := s.prev pos
    if p (s.get pos) then some pos
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
@[inline] def revFind (s : String) (p : Char → Bool) : Option Pos :=
  revFindAux s p s.endPos

/--
Returns either `p₁` or `p₂`, whichever has the least byte index.
-/
abbrev Pos.min (p₁ p₂ : Pos) : Pos :=
  { byteIdx := p₁.byteIdx.min p₂.byteIdx }

@[export lean_string_pos_min]
def Pos.Internal.minImpl (p₁ p₂ : Pos) : Pos :=
  Pos.min p₁ p₂

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
def firstDiffPos (a b : String) : Pos :=
  let stopPos := a.endPos.min b.endPos
  let rec loop (i : Pos) : Pos :=
    if h : i < stopPos then
      if a.get i != b.get i then i
      else
        have := Nat.sub_lt_sub_left h (lt_next a i)
        loop (a.next i)
    else i
    termination_by stopPos.1 - i.1
  loop 0

/--
Creates a new string that consists of the region of the input string delimited by the two positions.

The result is `""` if the start position is greater than or equal to the end position or if the
start position is at the end of the string. If either position is invalid (that is, if either points
at the middle of a multi-byte UTF-8 character) then the result is unspecified.

Examples:
* `"red green blue".extract ⟨0⟩ ⟨3⟩ = "red"`
* `"red green blue".extract ⟨3⟩ ⟨0⟩ = ""`
* `"red green blue".extract ⟨0⟩ ⟨100⟩ = "red green blue"`
* `"red green blue".extract ⟨4⟩ ⟨100⟩ = "green blue"`
* `"L∃∀N".extract ⟨2⟩ ⟨100⟩ = "green blue"`
-/
@[extern "lean_string_utf8_extract", expose]
def extract (s : String) (b e : Pos) : String :=
  if e ≤ b then
    ""
  else
    match s.pos? b with
    | none => ""
    | some b =>
      let e := (s.pos? e).getD s.endValidPos
      b.extract e

@[specialize] def splitAux (s : String) (p : Char → Bool) (b : Pos) (i : Pos) (r : List String) : List String :=
  if h : s.atEnd i then
    let r := (s.extract b i)::r
    r.reverse
  else
    have := Nat.sub_lt_sub_left (Nat.gt_of_not_le (mt decide_eq_true h)) (lt_next s _)
    if p (s.get i) then
      let i' := s.next i
      splitAux s p i' i' (s.extract b i :: r)
    else
      splitAux s p b (s.next i) r
termination_by s.endPos.1 - i.1

/--
Splits a string at each character for which `p` returns `true`.

The characters that satisfy `p` are not included in any of the resulting strings. If multiple
characters in a row satisfy `p`, then the resulting list will contain empty strings.

Examples:
* `"coffee tea water".split (·.isWhitespace) = ["coffee", "tea", "water"]`
* `"coffee  tea  water".split (·.isWhitespace) = ["coffee", "", "tea", "", "water"]`
* `"fun x =>\n  x + 1\n".split (· == '\n') = ["fun x =>", "  x + 1", ""]`
-/
@[specialize] def split (s : String) (p : Char → Bool) : List String :=
  splitAux s p 0 0 []

/--
Auxiliary for `splitOn`. Preconditions:
* `sep` is not empty
* `b <= i` are indexes into `s`
* `j` is an index into `sep`, and not at the end

It represents the state where we have currently parsed some split parts into `r` (in reverse order),
`b` is the beginning of the string / the end of the previous match of `sep`, and the first `j` bytes
of `sep` match the bytes `i-j .. i` of `s`.
-/
def splitOnAux (s sep : String) (b : Pos) (i : Pos) (j : Pos) (r : List String) : List String :=
  if s.atEnd i then
    let r := (s.extract b i)::r
    r.reverse
  else
    if s.get i == sep.get j then
      let i := s.next i
      let j := sep.next j
      if sep.atEnd j then
        splitOnAux s sep i i 0 (s.extract b (i - j)::r)
      else
        splitOnAux s sep b i j r
    else
      splitOnAux s sep b (s.next (i - j)) 0 r
termination_by (s.endPos.1 - (i - j).1, sep.endPos.1 - j.1)
decreasing_by
  focus
    rename_i h _ _
    left; exact Nat.sub_lt_sub_left
      (Nat.lt_of_le_of_lt (Nat.sub_le ..) (Nat.gt_of_not_le (mt decide_eq_true h)))
      (Nat.lt_of_le_of_lt (Nat.sub_le ..) (lt_next s _))
  focus
    rename_i i₀ j₀ _ eq h'
    rw [show (s.next i₀ - sep.next j₀).1 = (i₀ - j₀).1 by
      change (_ + Char.utf8Size _) - (_ + Char.utf8Size _) = _
      rw [(beq_iff_eq ..).1 eq, Nat.add_sub_add_right]; rfl]
    right; exact Nat.sub_lt_sub_left
      (Nat.lt_of_le_of_lt (Nat.le_add_right ..) (Nat.gt_of_not_le (mt decide_eq_true h')))
      (lt_next sep _)
  focus
    rename_i h _
    left; exact Nat.sub_lt_sub_left
      (Nat.lt_of_le_of_lt (Nat.sub_le ..) (Nat.gt_of_not_le (mt decide_eq_true h)))
      (lt_next s _)

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

instance : Inhabited String := ⟨""⟩

instance : Append String := ⟨String.append⟩

/--
Adds multiple repetitions of a character to the end of a string.

Returns `s`, with `n` repetitions of `c` at the end. Internally, the implementation repeatedly calls
`String.push`, so the string is modified in-place if there is a unique reference to it.

Examples:
 * `"indeed".pushn '!' 2 = "indeed!!"`
 * `"indeed".pushn '!' 0 = "indeed"`
 * `"".pushn ' ' 4 = "    "`
-/
@[inline] def pushn (s : String) (c : Char) (n : Nat) : String :=
  n.repeat (fun s => s.push c) s

@[export lean_string_pushn]
def Internal.pushnImpl (s : String) (c : Char) (n : Nat) : String :=
  String.pushn s c n

/--
Checks whether a string is empty.

Empty strings are equal to `""` and have length and end position `0`.

Examples:
 * `"".isEmpty = true`
 * `"empty".isEmpty = false`
 * `" ".isEmpty = false`
-/
@[inline] def isEmpty (s : String) : Bool :=
  s.endPos == 0

@[export lean_string_isempty]
def Internal.isEmptyImpl (s : String) : Bool :=
  String.isEmpty s

/--
Appends all the strings in a list of strings, in order.

Use `String.intercalate` to place a separator string between the strings in a list.

Examples:
 * `String.join ["gr", "ee", "n"] = "green"`
 * `String.join ["b", "", "l", "", "ue"] = "blue"`
 * `String.join [] = ""`
-/
@[inline] def join (l : List String) : String :=
  l.foldl (fun r s => r ++ s) ""

/--
Appends the strings in a list of strings, placing the separator `s` between each pair.

Examples:
 * `", ".intercalate ["red", "green", "blue"] = "red, green, blue"`
 * `" and ".intercalate ["tea", "coffee"] = "tea and coffee"`
 * `" | ".intercalate ["M", "", "N"] = "M |  | N"`
-/
def intercalate (s : String) : List String → String
  | []      => ""
  | a :: as => go a s as
where go (acc : String) (s : String) : List String → String
  | a :: as => go (acc ++ s ++ a) s as
  | []      => acc

@[export lean_string_intercalate]
def Internal.intercalateImpl (s : String) : List String → String :=
  String.intercalate s

/--
An iterator over the characters (Unicode code points) in a `String`. Typically created by
`String.iter`.

String iterators pair a string with a valid byte index. This allows efficient character-by-character
processing of strings while avoiding the need to manually ensure that byte indices are used with the
correct strings.

An iterator is *valid* if the position `i` is *valid* for the string `s`, meaning `0 ≤ i ≤ s.endPos`
and `i` lies on a UTF8 byte boundary. If `i = s.endPos`, the iterator is at the end of the string.

Most operations on iterators return unspecified values if the iterator is not valid. The functions
in the `String.Iterator` API rule out the creation of invalid iterators, with two exceptions:
- `Iterator.next iter` is invalid if `iter` is already at the end of the string (`iter.atEnd` is
  `true`), and
- `Iterator.forward iter n`/`Iterator.nextn iter n` is invalid if `n` is strictly greater than the
  number of remaining characters.
-/
structure Iterator where
  /-- The string being iterated over. -/
  s : String
  /-- The current UTF-8 byte position in the string `s`.

  This position is not guaranteed to be valid for the string. If the position is not valid, then the
  current character is `(default : Char)`, similar to `String.get` on an invalid position.
  -/
  i : Pos
  deriving DecidableEq, Inhabited

/-- Creates an iterator at the beginning of the string. -/
@[inline] def mkIterator (s : String) : Iterator :=
  ⟨s, 0⟩

@[inherit_doc mkIterator]
abbrev iter := mkIterator

/--
The size of a string iterator is the number of bytes remaining.

Recursive functions that iterate towards the end of a string will typically decrease this measure.
-/
instance : SizeOf String.Iterator where
  sizeOf i := i.1.utf8ByteSize - i.2.byteIdx

theorem Iterator.sizeOf_eq (i : String.Iterator) : sizeOf i = i.1.utf8ByteSize - i.2.byteIdx :=
  rfl

namespace Iterator
@[inline, inherit_doc Iterator.s]
def toString := Iterator.s

/--
The number of UTF-8 bytes remaining in the iterator.
-/
@[inline] def remainingBytes : Iterator → Nat
  | ⟨s, i⟩ => s.endPos.byteIdx - i.byteIdx

@[inline, inherit_doc Iterator.i]
def pos := Iterator.i

/--
Gets the character at the iterator's current position.

A run-time bounds check is performed. Use `String.Iterator.curr'` to avoid redundant bounds checks.

If the position is invalid, returns `(default : Char)`.
-/
@[inline] def curr : Iterator → Char
  | ⟨s, i⟩ => get s i

/--
Moves the iterator's position forward by one character, unconditionally.

It is only valid to call this function if the iterator is not at the end of the string (i.e.
if `Iterator.atEnd` is `false`); otherwise, the resulting iterator will be invalid.
-/
@[inline] def next : Iterator → Iterator
  | ⟨s, i⟩ => ⟨s, s.next i⟩

/--
Moves the iterator's position backward by one character, unconditionally.

The position is not changed if the iterator is at the beginning of the string.
-/
@[inline] def prev : Iterator → Iterator
  | ⟨s, i⟩ => ⟨s, s.prev i⟩

/--
Checks whether the iterator is past its string's last character.
-/
@[inline] def atEnd : Iterator → Bool
  | ⟨s, i⟩ => i.byteIdx ≥ s.endPos.byteIdx

/--
Checks whether the iterator is at or before the string's last character.
-/
@[inline] def hasNext : Iterator → Bool
  | ⟨s, i⟩ => i.byteIdx < s.endPos.byteIdx

/--
Checks whether the iterator is after the beginning of the string.
-/
@[inline] def hasPrev : Iterator → Bool
  | ⟨_, i⟩ => i.byteIdx > 0

/--
Gets the character at the iterator's current position.

The proof of `it.hasNext` ensures that there is, in fact, a character at the current position. This
function is faster that `String.Iterator.curr` due to avoiding a run-time bounds check.
-/
@[inline] def curr' (it : Iterator) (h : it.hasNext) : Char :=
  match it with
  | ⟨s, i⟩ => get' s i (by simpa only [hasNext, endPos, decide_eq_true_eq, String.atEnd, ge_iff_le, Nat.not_le] using h)

/--
Moves the iterator's position forward by one character, unconditionally.

The proof of `it.hasNext` ensures that there is, in fact, a position that's one character forwards.
This function is faster that `String.Iterator.next` due to avoiding a run-time bounds check.
-/
@[inline] def next' (it : Iterator) (h : it.hasNext) : Iterator :=
  match it with
  | ⟨s, i⟩ => ⟨s, s.next' i (by simpa only [hasNext, endPos, decide_eq_true_eq, String.atEnd, ge_iff_le, Nat.not_le] using h)⟩

/--
Replaces the current character in the string.

Does nothing if the iterator is at the end of the string. If both the replacement character and the
replaced character are 7-bit ASCII characters and the string is not shared, then it is updated
in-place and not copied.
-/
@[inline] def setCurr : Iterator → Char → Iterator
  | ⟨s, i⟩, c => ⟨s.set i c, i⟩

/--
Moves the iterator's position to the end of the string, just past the last character.
-/
@[inline] def toEnd : Iterator → Iterator
  | ⟨s, _⟩ => ⟨s, s.endPos⟩

/--
Extracts the substring between the positions of two iterators. The first iterator's position is the
start of the substring, and the second iterator's position is the end.

Returns the empty string if the iterators are for different strings, or if the position of the first
iterator is past the position of the second iterator.
-/
@[inline] def extract : Iterator → Iterator → String
  | ⟨s₁, b⟩, ⟨s₂, e⟩ =>
    if s₁ ≠ s₂ || b > e then ""
    else s₁.extract b e

/--
Moves the iterator's position forward by the specified number of characters.

The resulting iterator is only valid if the number of characters to skip is less than or equal
to the number of characters left in the iterator.
-/
def forward : Iterator → Nat → Iterator
  | it, 0   => it
  | it, n+1 => forward it.next n

/--
The remaining characters in an iterator, as a string.
-/
@[inline] def remainingToString : Iterator → String
  | ⟨s, i⟩ => s.extract i s.endPos

@[inherit_doc forward]
def nextn : Iterator → Nat → Iterator
  | it, 0   => it
  | it, i+1 => nextn it.next i

/--
Moves the iterator's position back by the specified number of characters, stopping at the beginning
of the string.
-/
def prevn : Iterator → Nat → Iterator
  | it, 0   => it
  | it, i+1 => prevn it.prev i
end Iterator

def offsetOfPosAux (s : String) (pos : Pos) (i : Pos) (offset : Nat) : Nat :=
  if i >= pos then offset
  else if h : s.atEnd i then
    offset
  else
    have := Nat.sub_lt_sub_left (Nat.gt_of_not_le (mt decide_eq_true h)) (lt_next s _)
    offsetOfPosAux s pos (s.next i) (offset+1)
termination_by s.endPos.1 - i.1

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
@[inline] def offsetOfPos (s : String) (pos : Pos) : Nat :=
  offsetOfPosAux s pos 0 0

@[export lean_string_offsetofpos]
def Internal.offsetOfPosImpl (s : String) (pos : Pos) : Nat :=
  String.offsetOfPos s pos

@[specialize] def foldlAux {α : Type u} (f : α → Char → α) (s : String) (stopPos : Pos) (i : Pos) (a : α) : α :=
  if h : i < stopPos then
    have := Nat.sub_lt_sub_left h (lt_next s i)
    foldlAux f s stopPos (s.next i) (f a (s.get i))
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
  foldlAux f s s.endPos 0 init

@[export lean_string_foldl]
def Internal.foldlImpl (f : String → Char → String) (init : String) (s : String) : String :=
  String.foldl f init s

@[specialize] def foldrAux {α : Type u} (f : Char → α → α) (a : α) (s : String) (i begPos : Pos) : α :=
  if h : begPos < i then
    have := String.prev_lt_of_pos s i <| mt (congrArg String.Pos.byteIdx) <|
      Ne.symm <| Nat.ne_of_lt <| Nat.lt_of_le_of_lt (Nat.zero_le _) h
    let i := s.prev i
    let a := f (s.get i) a
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
  foldrAux f init s s.endPos 0

@[specialize] def anyAux (s : String) (stopPos : Pos) (p : Char → Bool) (i : Pos) : Bool :=
  if h : i < stopPos then
    if p (s.get i) then true
    else
      have := Nat.sub_lt_sub_left h (lt_next s i)
      anyAux s stopPos p (s.next i)
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
  anyAux s s.endPos p 0

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

theorem utf8SetAux_of_gt (c' : Char) : ∀ (cs : List Char) {i p : Pos}, i > p → utf8SetAux c' cs i p = cs
  | [],    _, _, _ => rfl
  | c::cs, i, p, h => by
    rw [utf8SetAux, if_neg (mt (congrArg (·.1)) (Ne.symm <| Nat.ne_of_lt h)), utf8SetAux_of_gt c' cs]
    exact Nat.lt_of_lt_of_le h (Nat.le_add_right ..)

theorem set_next_add (s : String) (i : Pos) (c : Char) (b₁ b₂)
    (h : (s.next i).1 + b₁ = s.endPos.1 + b₂) :
    ((s.set i c).next i).1 + b₁ = (s.set i c).endPos.1 + b₂ := by
  simp [next, get, set, endPos, ← utf8ByteSize'_eq, utf8ByteSize'] at h ⊢
  rw [Nat.add_comm i.1, Nat.add_assoc] at h ⊢
  let rec foo : ∀ cs a b₁ b₂,
    (utf8GetAux cs a i).utf8Size + b₁ = utf8ByteSize'.go cs + b₂ →
    (utf8GetAux (utf8SetAux c cs a i) a i).utf8Size + b₁ = utf8ByteSize'.go (utf8SetAux c cs a i) + b₂
  | [], _, _, _, h => h
  | c'::cs, a, b₁, b₂, h => by
    unfold utf8SetAux
    apply iteInduction (motive := fun p => (utf8GetAux p a i).utf8Size + b₁ = utf8ByteSize'.go p + b₂) <;>
      intro h' <;> simp [utf8GetAux, h', utf8ByteSize'.go] at h ⊢
    next =>
      rw [Nat.add_assoc, Nat.add_left_comm] at h ⊢; rw [Nat.add_left_cancel h]
    next =>
      rw [Nat.add_assoc] at h ⊢
      refine foo cs (a + c') b₁ (c'.utf8Size + b₂) h
  exact foo s.data 0 _ _ h

theorem mapAux_lemma (s : String) (i : Pos) (c : Char) (h : ¬s.atEnd i) :
    (s.set i c).endPos.1 - ((s.set i c).next i).1 < s.endPos.1 - i.1 := by
  suffices (s.set i c).endPos.1 - ((s.set i c).next i).1 = s.endPos.1 - (s.next i).1 by
    rw [this]
    apply Nat.sub_lt_sub_left (Nat.gt_of_not_le (mt decide_eq_true h)) (lt_next ..)
  have := set_next_add s i c (s.endPos.byteIdx - (s.next i).byteIdx) 0
  have := set_next_add s i c 0 ((s.next i).byteIdx - s.endPos.byteIdx)
  omega

@[specialize] def mapAux (f : Char → Char) (i : Pos) (s : String) : String :=
  if h : s.atEnd i then s
  else
    let c := f (s.get i)
    have := mapAux_lemma s i c h
    let s := s.set i c
    mapAux f (s.next i) s
termination_by s.endPos.1 - i.1

/--
Applies the function `f` to every character in a string, returning a string that contains the
resulting characters.

Examples:
 * `"abc123".map Char.toUpper = "ABC123"`
 * `"".map Char.toUpper = ""`
-/
@[inline] def map (f : Char → Char) (s : String) : String :=
  mapAux f 0 s

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
-/
def substrEq (s1 : String) (pos1 : String.Pos) (s2 : String) (pos2 : String.Pos) (sz : Nat) : Bool :=
  pos1.byteIdx + sz ≤ s1.endPos.byteIdx && pos2.byteIdx + sz ≤ s2.endPos.byteIdx && loop pos1 pos2 { byteIdx := pos1.byteIdx + sz }
where
  loop (off1 off2 stop1 : Pos) :=
    if _h : off1.byteIdx < stop1.byteIdx then
      let c₁ := s1.get off1
      let c₂ := s2.get off2
      c₁ == c₂ && loop (off1 + c₁) (off2 + c₂) stop1
    else true
  termination_by stop1.1 - off1.1
  decreasing_by
    have := Nat.sub_lt_sub_left _h (Nat.add_lt_add_left c₁.utf8Size_pos off1.1)
    decreasing_tactic

/--
Checks whether the first string (`p`) is a prefix of the second (`s`).

`String.startsWith` is a version that takes the potential prefix after the string.

Examples:
 * `"red".isPrefixOf "red green blue" = true`
 * `"green".isPrefixOf "red green blue" = false`
 * `"".isPrefixOf "red green blue" = true`
-/
def isPrefixOf (p : String) (s : String) : Bool :=
  substrEq p 0 s 0 p.endPos.byteIdx

@[export lean_string_isprefixof]
def Internal.isPrefixOfImpl (p : String) (s : String) : Bool :=
  String.isPrefixOf p s

/--
In the string `s`, replaces all occurrences of `pattern` with `replacement`.

Examples:
* `"red green blue".replace "e" "" = "rd grn blu"`
* `"red green blue".replace "ee" "E" = "red grEn blue"`
* `"red green blue".replace "e" "E" = "rEd grEEn bluE"`
-/
def replace (s pattern replacement : String) : String :=
  if h : pattern.endPos.1 = 0 then s
  else
    have hPatt := Nat.zero_lt_of_ne_zero h
    let rec loop (acc : String) (accStop pos : String.Pos) :=
      if h : pos.byteIdx + pattern.endPos.byteIdx > s.endPos.byteIdx then
        acc ++ s.extract accStop s.endPos
      else
        have := Nat.lt_of_lt_of_le (Nat.add_lt_add_left hPatt _) (Nat.ge_of_not_lt h)
        if s.substrEq pos pattern 0 pattern.endPos.byteIdx then
          have := Nat.sub_lt_sub_left this (Nat.add_lt_add_left hPatt _)
          loop (acc ++ s.extract accStop pos ++ replacement) (pos + pattern) (pos + pattern)
        else
          have := Nat.sub_lt_sub_left this (lt_next s pos)
          loop acc accStop (s.next pos)
      termination_by s.endPos.1 - pos.1
    loop "" 0 0

/--
Returns the position of the beginning of the line that contains the position `pos`.

Lines are ended by `'\n'`, and the returned position is either `0 : String.Pos` or immediately after
a `'\n'` character.
-/
def findLineStart (s : String) (pos : String.Pos) : String.Pos :=
  match s.revFindAux (· = '\n') pos with
  | none => 0
  | some n => ⟨n.byteIdx + 1⟩

end String

namespace Substring

/--
Checks whether a substring is empty.

A substring is empty if its start and end positions are the same.
-/
@[inline] def isEmpty (ss : Substring) : Bool :=
  ss.bsize == 0

@[export lean_substring_isempty]
def Internal.isEmptyImpl (ss : Substring) : Bool :=
  Substring.isEmpty ss

/--
Copies the region of the underlying string pointed to by a substring into a fresh string.
-/
@[inline] def toString : Substring → String
  | ⟨s, b, e⟩ => s.extract b e

@[export lean_substring_tostring]
def Internal.toStringImpl : Substring → String :=
  Substring.toString

/--
Returns an iterator into the underlying string, at the substring's starting position. The ending
position is discarded, so the iterator alone cannot be used to determine whether its current
position is within the original substring.
-/
@[inline] def toIterator : Substring → String.Iterator
  | ⟨s, b, _⟩ => ⟨s, b⟩

/--
Returns the character at the given position in the substring.

The position is relative to the substring, rather than the underlying string, and no bounds checking
is performed with respect to the substring's end position. If the relative position is not a valid
position in the underlying string, the fallback value `(default : Char)`, which is `'A'`, is
returned.  Does not panic.
-/
@[inline] def get : Substring → String.Pos → Char
  | ⟨s, b, _⟩, p => s.get (b+p)

@[export lean_substring_get]
def Internal.getImpl : Substring → String.Pos → Char :=
  Substring.get

/--
Returns the next position in a substring after the given position. If the position is at the end of
the substring, it is returned unmodified.

Both the input position and the returned position are interpreted relative to the substring's start
position, not the underlying string.
-/
@[inline] def next : Substring → String.Pos → String.Pos
  | ⟨s, b, e⟩, p =>
    let absP := b+p
    if absP = e then p else { byteIdx := (s.next absP).byteIdx - b.byteIdx }

theorem lt_next (s : Substring) (i : String.Pos) (h : i.1 < s.bsize) :
    i.1 < (s.next i).1 := by
  simp [next]; rw [if_neg ?a]
  case a =>
    refine mt (congrArg String.Pos.byteIdx) (Nat.ne_of_lt ?_)
    exact (Nat.add_comm .. ▸ Nat.add_lt_of_lt_sub h :)
  apply Nat.lt_sub_of_add_lt
  rw [Nat.add_comm]; apply String.lt_next

/--
Returns the previous position in a substring, just prior to the given position. If the position is
at the beginning of the substring, it is returned unmodified.

Both the input position and the returned position are interpreted relative to the substring's start
position, not the underlying string.
-/
@[inline] def prev : Substring → String.Pos → String.Pos
  | ⟨s, b, _⟩, p =>
    let absP := b+p
    if absP = b then p else { byteIdx := (s.prev absP).byteIdx - b.byteIdx }

@[export lean_substring_prev]
def Internal.prevImpl : Substring → String.Pos → String.Pos :=
  Substring.prev

/--
Returns the position that's the specified number of characters forward from the given position in a
substring. If the end position of the substring is reached, it is returned.

Both the input position and the returned position are interpreted relative to the substring's start
position, not the underlying string.
-/
def nextn : Substring → Nat → String.Pos → String.Pos
  | _,  0,   p => p
  | ss, i+1, p => ss.nextn i (ss.next p)

/--
Returns the position that's the specified number of characters prior to the given position in a
substring. If the start position of the substring is reached, it is returned.

Both the input position and the returned position are interpreted relative to the substring's start
position, not the underlying string.
-/
def prevn : Substring → Nat → String.Pos → String.Pos
  | _,  0,   p => p
  | ss, i+1, p => ss.prevn i (ss.prev p)

/--
Returns the first character in the substring.

If the substring is empty, but the substring's start position is a valid position in the underlying
string, then the character at the start position is returned. If the substring's start position is
not a valid position in the string, the fallback value `(default : Char)`, which is `'A'`, is
returned.  Does not panic.
-/
@[inline, expose] def front (s : Substring) : Char :=
  s.get 0

@[export lean_substring_front]
def Internal.frontImpl : Substring → Char :=
  Substring.front

/--
Returns the substring-relative position of the first occurrence of `c` in `s`, or `s.bsize` if `c`
doesn't occur.
-/
@[inline] def posOf (s : Substring) (c : Char) : String.Pos :=
  match s with
  | ⟨s, b, e⟩ => { byteIdx := (String.posOfAux s c e b).byteIdx - b.byteIdx }

/--
Removes the specified number of characters (Unicode code points) from the beginning of a substring
by advancing its start position.

If the substring's end position is reached, the start position is not advanced past it.
-/
@[inline] def drop : Substring → Nat → Substring
  | ss@⟨s, b, e⟩, n => ⟨s, b + ss.nextn n 0, e⟩

@[export lean_substring_drop]
def Internal.dropImpl : Substring → Nat → Substring :=
  Substring.drop

/--
Removes the specified number of characters (Unicode code points) from the end of a substring
by moving its end position towards its start position.

If the substring's start position is reached, the end position is not retracted past it.
-/
@[inline] def dropRight : Substring → Nat → Substring
  | ss@⟨s, b, _⟩, n => ⟨s, b, b + ss.prevn n ⟨ss.bsize⟩⟩

/--
Retains only the specified number of characters (Unicode code points) at the beginning of a
substring, by moving its end position towards its start position.

If the substring's start position is reached, the end position is not retracted past it.
-/
@[inline] def take : Substring → Nat → Substring
  | ss@⟨s, b, _⟩, n => ⟨s, b, b + ss.nextn n 0⟩

/--
Retains only the specified number of characters (Unicode code points) at the end of a substring, by
moving its start position towards its end position.

If the substring's end position is reached, the start position is not advanced past it.
-/
@[inline] def takeRight : Substring → Nat → Substring
  | ss@⟨s, b, e⟩, n => ⟨s, b + ss.prevn n ⟨ss.bsize⟩, e⟩

/--
Checks whether a position in a substring is precisely equal to its ending position.

The position is understood relative to the substring's starting position, rather than the underlying
string's starting position.
-/
@[inline] def atEnd : Substring → String.Pos → Bool
  | ⟨_, b, e⟩, p => b + p == e

/--
Returns the region of the substring delimited by the provided start and stop positions, as a
substring. The positions are interpreted with respect to the substring's start position, rather than
the underlying string.

If the resulting substring is empty, then the resulting substring is a substring of the empty string
`""`. Otherwise, the underlying string is that of the input substring with the beginning and end
positions adjusted.
-/
@[inline] def extract : Substring → String.Pos → String.Pos → Substring
  | ⟨s, b, e⟩, b', e' => if b' ≥ e' then ⟨"", 0, 0⟩ else ⟨s, e.min (b+b'), e.min (b+e')⟩

@[export lean_substring_extract]
def Internal.extractImpl : Substring → String.Pos → String.Pos → Substring :=
  Substring.extract

/--
Splits a substring `s` on occurrences of the separator string `sep`. The default separator is `" "`.

When `sep` is empty, the result is `[s]`. When `sep` occurs in overlapping patterns, the first match
is taken. There will always be exactly `n+1` elements in the returned list if there were `n`
non-overlapping matches of `sep` in the string. The separators are not included in the returned
substrings, which are all substrings of `s`'s string.
-/
def splitOn (s : Substring) (sep : String := " ") : List Substring :=
  if sep == "" then
    [s]
  else
    let rec loop (b i j : String.Pos) (r : List Substring) : List Substring :=
      if h : i.byteIdx < s.bsize then
        have := Nat.sub_lt_sub_left h (lt_next s i h)
        if s.get i == sep.get j then
          let i := s.next i
          let j := sep.next j
          if sep.atEnd j then
            loop i i 0 (s.extract b (i-j) :: r)
          else
            loop b i j r
        else
          loop b (s.next i) 0 r
      else
        let r := if sep.atEnd j then
          "".toSubstring :: s.extract b (i-j) :: r
        else
          s.extract b i :: r
        r.reverse
      termination_by s.bsize - i.1
    loop 0 0 0 []

/--
Folds a function over a substring from the left, accumulating a value starting with `init`. The
accumulated value is combined with each character in order, using `f`.
-/
@[inline] def foldl {α : Type u} (f : α → Char → α) (init : α) (s : Substring) : α :=
  match s with
  | ⟨s, b, e⟩ => String.foldlAux f s e b init

/--
Folds a function over a substring from the right, accumulating a value starting with `init`. The
accumulated value is combined with each character in reverse order, using `f`.
-/
@[inline] def foldr {α : Type u} (f : Char → α → α) (init : α) (s : Substring) : α :=
  match s with
  | ⟨s, b, e⟩ => String.foldrAux f init s e b

/--
Checks whether the Boolean predicate `p` returns `true` for any character in a substring.

Short-circuits at the first character for which `p` returns `true`.
-/
@[inline] def any (s : Substring) (p : Char → Bool) : Bool :=
  match s with
  | ⟨s, b, e⟩ => String.anyAux s e p b

/--
Checks whether the Boolean predicate `p` returns `true` for every character in a substring.

Short-circuits at the first character for which `p` returns `false`.
-/
@[inline] def all (s : Substring) (p : Char → Bool) : Bool :=
  !s.any (fun c => !p c)

@[export lean_substring_all]
def Internal.allImpl (s : Substring) (p : Char → Bool) : Bool :=
  Substring.all s p

/--
Checks whether a substring contains the specified character.
-/
@[inline] def contains (s : Substring) (c : Char) : Bool :=
  s.any (fun a => a == c)

@[specialize] def takeWhileAux (s : String) (stopPos : String.Pos) (p : Char → Bool) (i : String.Pos) : String.Pos :=
  if h : i < stopPos then
    if p (s.get i) then
      have := Nat.sub_lt_sub_left h (String.lt_next s i)
      takeWhileAux s stopPos p (s.next i)
    else i
  else i
termination_by stopPos.1 - i.1

/--
Retains only the longest prefix of a substring in which a Boolean predicate returns `true` for all
characters by moving the substring's end position towards its start position.
-/
@[inline] def takeWhile : Substring → (Char → Bool) → Substring
  | ⟨s, b, e⟩, p =>
    let e := takeWhileAux s e p b;
    ⟨s, b, e⟩

@[export lean_substring_takewhile]
def Internal.takeWhileImpl : Substring → (Char → Bool) → Substring :=
  Substring.takeWhile

/--
Removes the longest prefix of a substring in which a Boolean predicate returns `true` for all
characters by moving the substring's start position. The start position is moved to the position of
the first character for which the predicate returns `false`, or to the substring's end position if
the predicate always returns `true`.
-/
@[inline] def dropWhile : Substring → (Char → Bool) → Substring
  | ⟨s, b, e⟩, p =>
    let b := takeWhileAux s e p b;
    ⟨s, b, e⟩

@[specialize] def takeRightWhileAux (s : String) (begPos : String.Pos) (p : Char → Bool) (i : String.Pos) : String.Pos :=
  if h : begPos < i then
    have := String.prev_lt_of_pos s i <| mt (congrArg String.Pos.byteIdx) <|
      Ne.symm <| Nat.ne_of_lt <| Nat.lt_of_le_of_lt (Nat.zero_le _) h
    let i' := s.prev i
    let c  := s.get i'
    if !p c then i
    else takeRightWhileAux s begPos p i'
  else i
termination_by i.1

/--
Retains only the longest suffix of a substring in which a Boolean predicate returns `true` for all
characters by moving the substring's start position towards its end position.
-/
@[inline] def takeRightWhile : Substring → (Char → Bool) → Substring
  | ⟨s, b, e⟩, p =>
    let b := takeRightWhileAux s b p e
    ⟨s, b, e⟩

/--
Removes the longest suffix of a substring in which a Boolean predicate returns `true` for all
characters by moving the substring's end position. The end position is moved just after the position
of the last character for which the predicate returns `false`, or to the substring's start position
if the predicate always returns `true`.
-/
@[inline] def dropRightWhile : Substring → (Char → Bool) → Substring
  | ⟨s, b, e⟩, p =>
    let e := takeRightWhileAux s b p e
    ⟨s, b, e⟩

/--
Removes leading whitespace from a substring by moving its start position to the first non-whitespace
character, or to its end position if there is no non-whitespace character.

“Whitespace” is defined as characters for which `Char.isWhitespace` returns `true`.
-/
@[inline] def trimLeft (s : Substring) : Substring :=
  s.dropWhile Char.isWhitespace

/--
Removes trailing whitespace from a substring by moving its end position to the last non-whitespace
character, or to its start position if there is no non-whitespace character.

“Whitespace” is defined as characters for which `Char.isWhitespace` returns `true`.
-/
@[inline] def trimRight (s : Substring) : Substring :=
  s.dropRightWhile Char.isWhitespace

/--
Removes leading and trailing whitespace from a substring by first moving its start position to the
first non-whitespace character, and then moving its end position to the last non-whitespace
character.

If the substring consists only of whitespace, then the resulting substring's start position is moved
to its end position.

“Whitespace” is defined as characters for which `Char.isWhitespace` returns `true`.

Examples:
 * `" red green blue ".toSubstring.trim.toString = "red green blue"`
 * `" red green blue ".toSubstring.trim.startPos = ⟨1⟩`
 * `" red green blue ".toSubstring.trim.stopPos = ⟨15⟩`
 * `"     ".toSubstring.trim.startPos = ⟨5⟩`
-/
@[inline] def trim : Substring → Substring
  | ⟨s, b, e⟩ =>
    let b := takeWhileAux s e Char.isWhitespace b
    let e := takeRightWhileAux s b Char.isWhitespace e
    ⟨s, b, e⟩

/--
Checks whether the substring can be interpreted as the decimal representation of a natural number.

A substring can be interpreted as a decimal natural number if it is not empty and all the characters
in it are digits.

Use `Substring.toNat?` to convert such a substring to a natural number.
-/
@[inline] def isNat (s : Substring) : Bool :=
  !s.isEmpty && s.all fun c => c.isDigit

/--
Checks whether the substring can be interpreted as the decimal representation of a natural number,
returning the number if it can.

A substring can be interpreted as a decimal natural number if it is not empty and all the characters
in it are digits.

Use `Substring.isNat` to check whether the substring is such a substring.
-/
def toNat? (s : Substring) : Option Nat :=
  if s.isNat then
    some <| s.foldl (fun n c => n*10 + (c.toNat - '0'.toNat)) 0
  else
    none

/--
Checks whether two substrings represent equal strings. Usually accessed via the `==` operator.

Two substrings do not need to have the same underlying string or the same start and end positions;
instead, they are equal if they contain the same sequence of characters.
-/
def beq (ss1 ss2 : Substring) : Bool :=
  ss1.bsize == ss2.bsize && ss1.str.substrEq ss1.startPos ss2.str ss2.startPos ss1.bsize

@[export lean_substring_beq]
def Internal.beqImpl (ss1 ss2 : Substring) : Bool :=
  Substring.beq ss1 ss2

instance hasBeq : BEq Substring := ⟨beq⟩

/--
Checks whether two substrings have the same position and content.

The two substrings do not need to have the same underlying string for this check to succeed.
-/
def sameAs (ss1 ss2 : Substring) : Bool :=
  ss1.startPos == ss2.startPos && ss1 == ss2

/--
Returns the longest common prefix of two substrings.

The returned substring uses the same underlying string as `s`.
-/
def commonPrefix (s t : Substring) : Substring :=
  { s with stopPos := loop s.startPos t.startPos }
where
  /-- Returns the ending position of the common prefix, working up from `spos, tpos`. -/
  loop spos tpos :=
    if h : spos < s.stopPos ∧ tpos < t.stopPos then
      if s.str.get spos == t.str.get tpos then
        have := Nat.sub_lt_sub_left h.1 (s.str.lt_next spos)
        loop (s.str.next spos) (t.str.next tpos)
      else
        spos
    else
      spos
  termination_by s.stopPos.byteIdx - spos.byteIdx

/--
Returns the longest common suffix of two substrings.

The returned substring uses the same underlying string as `s`.
-/
def commonSuffix (s t : Substring) : Substring :=
  { s with startPos := loop s.stopPos t.stopPos }
where
  /-- Returns the starting position of the common prefix, working down from `spos, tpos`. -/
  loop spos tpos :=
    if h : s.startPos < spos ∧ t.startPos < tpos then
      let spos' := s.str.prev spos
      let tpos' := t.str.prev tpos
      if s.str.get spos' == t.str.get tpos' then
        have : spos' < spos := s.str.prev_lt_of_pos spos (String.Pos.ne_zero_of_lt h.1)
        loop spos' tpos'
      else
        spos
    else
      spos
  termination_by spos.byteIdx

/--
If `pre` is a prefix of `s`, returns the remainder. Returns `none` otherwise.

The substring `pre` is a prefix of `s` if there exists a `t : Substring` such that
`s.toString = pre.toString ++ t.toString`. If so, the result is the substring of `s` without the
prefix.
-/
def dropPrefix? (s : Substring) (pre : Substring) : Option Substring :=
  let t := s.commonPrefix pre
  if t.bsize = pre.bsize then
    some { s with startPos := t.stopPos }
  else
    none

/--
If `suff` is a suffix of `s`, returns the remainder. Returns `none` otherwise.

The substring `suff` is a suffix of `s` if there exists a `t : Substring` such that
`s.toString = t.toString ++ suff.toString`. If so, the result the substring of `s` without the
suffix.
-/
def dropSuffix? (s : Substring) (suff : Substring) : Option Substring :=
  let t := s.commonSuffix suff
  if t.bsize = suff.bsize then
    some { s with stopPos := t.startPos }
  else
    none

end Substring

namespace String

/--
Removes the specified number of characters (Unicode code points) from the start of the string.

If `n` is greater than `s.length`, returns `""`.

Examples:
 * `"red green blue".drop 4 = "green blue"`
 * `"red green blue".drop 10 = "blue"`
 * `"red green blue".drop 50 = ""`
-/
@[inline] def drop (s : String) (n : Nat) : String :=
  (s.toSubstring.drop n).toString

@[export lean_string_drop]
def Internal.dropImpl (s : String) (n : Nat) : String :=
  String.drop s n

/--
Removes the specified number of characters (Unicode code points) from the end of the string.

If `n` is greater than `s.length`, returns `""`.

Examples:
 * `"red green blue".dropRight 5 = "red green"`
 * `"red green blue".dropRight 11 = "red"`
 * `"red green blue".dropRight 50 = ""`
-/
@[inline] def dropRight (s : String) (n : Nat) : String :=
  (s.toSubstring.dropRight n).toString

@[export lean_string_dropright]
def Internal.dropRightImpl (s : String) (n : Nat) : String :=
  String.dropRight s n

/--
Creates a new string that contains the first `n` characters (Unicode code points) of `s`.

If `n` is greater than `s.length`, returns `s`.

Examples:
* `"red green blue".take 3 = "red"`
* `"red green blue".take 1 = "r"`
* `"red green blue".take 0 = ""`
* `"red green blue".take 100 = "red green blue"`
-/
@[inline] def take (s : String) (n : Nat) : String :=
  (s.toSubstring.take n).toString

/--
Creates a new string that contains the last `n` characters (Unicode code points) of `s`.

If `n` is greater than `s.length`, returns `s`.

Examples:
* `"red green blue".takeRight 4 = "blue"`
* `"red green blue".takeRight 1 = "e"`
* `"red green blue".takeRight 0 = ""`
* `"red green blue".takeRight 100 = "red green blue"`
-/
@[inline] def takeRight (s : String) (n : Nat) : String :=
  (s.toSubstring.takeRight n).toString

/--
Creates a new string that contains the longest prefix of `s` in which `p` returns `true` for all
characters.

Examples:
* `"red green blue".takeWhile (·.isLetter) = "red"`
* `"red green blue".takeWhile (· == 'r') = "r"`
* `"red green blue".takeWhile (· != 'n') = "red gree"`
* `"red green blue".takeWhile (fun _ => true) = "red green blue"`
-/
@[inline] def takeWhile (s : String) (p : Char → Bool) : String :=
  (s.toSubstring.takeWhile p).toString

/--
Creates a new string by removing the longest prefix from `s` in which `p` returns `true` for all
characters.

Examples:
* `"red green blue".dropWhile (·.isLetter) = " green blue"`
* `"red green blue".dropWhile (· == 'r') = "ed green blue"`
* `"red green blue".dropWhile (· != 'n') = "n blue"`
* `"red green blue".dropWhile (fun _ => true) = ""`
-/
@[inline] def dropWhile (s : String) (p : Char → Bool) : String :=
  (s.toSubstring.dropWhile p).toString

/--
Creates a new string that contains the longest suffix of `s` in which `p` returns `true` for all
characters.

Examples:
* `"red green blue".takeRightWhile (·.isLetter) = "blue"`
* `"red green blue".takeRightWhile (· == 'e') = "e"`
* `"red green blue".takeRightWhile (· != 'n') = " blue"`
* `"red green blue".takeRightWhile (fun _ => true) = "red green blue"`
-/
@[inline] def takeRightWhile (s : String) (p : Char → Bool) : String :=
  (s.toSubstring.takeRightWhile p).toString

/--
Creates a new string by removing the longest suffix from `s` in which `p` returns `true` for all
characters.

Examples:
* `"red green blue".dropRightWhile (·.isLetter) = "red green "`
* `"red green blue".dropRightWhile (· == 'e') = "red green blu"`
* `"red green blue".dropRightWhile (· != 'n') = "red green"`
* `"red green blue".dropRightWhile (fun _ => true) = ""`
-/
@[inline] def dropRightWhile (s : String) (p : Char → Bool) : String :=
  (s.toSubstring.dropRightWhile p).toString

/--
Checks whether the first string (`s`) begins with the second (`pre`).

`String.isPrefix` is a version that takes the potential prefix before the string.

Examples:
 * `"red green blue".startsWith "red" = true`
 * `"red green blue".startsWith "green" = false`
 * `"red green blue".startsWith "" = true`
 * `"red".startsWith "red" = true`
-/
@[inline] def startsWith (s pre : String) : Bool :=
  s.toSubstring.take pre.length == pre.toSubstring

/--
Checks whether the first string (`s`) ends with the second (`post`).

Examples:
 * `"red green blue".endsWith "blue" = true`
 * `"red green blue".endsWith "green" = false`
 * `"red green blue".endsWith "" = true`
 * `"red".endsWith "red" = true`
-/
@[inline] def endsWith (s post : String) : Bool :=
  s.toSubstring.takeRight post.length == post.toSubstring

/--
Removes trailing whitespace from a string.

“Whitespace” is defined as characters for which `Char.isWhitespace` returns `true`.

Examples:
* `"abc".trimRight = "abc"`
* `"   abc".trimRight = "   abc"`
* `"abc \t  ".trimRight = "abc"`
* `"  abc   ".trimRight = "  abc"`
* `"abc\ndef\n".trimRight = "abc\ndef"`
-/
@[inline] def trimRight (s : String) : String :=
  s.toSubstring.trimRight.toString

/--
Removes leading whitespace from a string.

“Whitespace” is defined as characters for which `Char.isWhitespace` returns `true`.

Examples:
* `"abc".trimLeft = "abc"`
* `"   abc".trimLeft = "   abc"`
* `"abc \t  ".trimLeft = "abc \t  "`
* `"  abc   ".trimLeft = "abc   "`
* `"abc\ndef\n".trimLeft = "abc\ndef\n"`
-/
@[inline] def trimLeft (s : String) : String :=
  s.toSubstring.trimLeft.toString

/--
Removes leading and trailing whitespace from a string.

“Whitespace” is defined as characters for which `Char.isWhitespace` returns `true`.

Examples:
* `"abc".trim = "abc"`
* `"   abc".trim = "abc"`
* `"abc \t  ".trim = "abc"`
* `"  abc   ".trim = "abc"`
* `"abc\ndef\n".trim = "abc\ndef"`
-/
@[inline] def trim (s : String) : String :=
  s.toSubstring.trim.toString

@[export lean_string_trim]
def Internal.trimImpl (s : String) : String :=
  String.trim s

/--
Repeatedly increments a position in a string, as if by `String.next`, while the predicate `p`
returns `true` for the character at the position. Stops incrementing at the end of the string or
when `p` returns `false` for the current character.

Examples:
* `let s := "   a  "; s.get (s.nextWhile Char.isWhitespace 0) = 'a'`
* `let s := "a  "; s.get (s.nextWhile Char.isWhitespace 0) = 'a'`
* `let s := "ba  "; s.get (s.nextWhile Char.isWhitespace 0) = 'b'`
-/
@[inline] def nextWhile (s : String) (p : Char → Bool) (i : String.Pos) : String.Pos :=
  Substring.takeWhileAux s s.endPos p i

@[export lean_string_nextwhile]
def Internal.nextWhileImpl (s : String) (p : Char → Bool) (i : String.Pos) : String.Pos :=
  String.nextWhile s p i

/--
Repeatedly increments a position in a string, as if by `String.next`, while the predicate `p`
returns `false` for the character at the position. Stops incrementing at the end of the string or
when `p` returns `true` for the current character.

Examples:
* `let s := "   a  "; s.get (s.nextUntil Char.isWhitespace 0) = ' '`
* `let s := "   a  "; s.get (s.nextUntil Char.isLetter 0) = 'a'`
* `let s := "a  "; s.get (s.nextUntil Char.isWhitespace 0) = ' '`
-/
@[inline] def nextUntil (s : String) (p : Char → Bool) (i : String.Pos) : String.Pos :=
  nextWhile s (fun c => !p c) i

/--
Replaces each character in `s` with the result of applying `Char.toUpper` to it.

`Char.toUpper` has no effect on characters outside of the range `'a'`–`'z'`.

Examples:
* `"orange".toUpper = "ORANGE"`
* `"abc123".toUpper = "ABC123"`
-/
@[inline] def toUpper (s : String) : String :=
  s.map Char.toUpper

/--
Replaces each character in `s` with the result of applying `Char.toLower` to it.

`Char.toLower` has no effect on characters outside of the range `'A'`–`'Z'`.

Examples:
* `"ORANGE".toLower = "orange"`
* `"Orange".toLower = "orange"`
* `"ABc123".toLower = "abc123"`
-/
@[inline] def toLower (s : String) : String :=
  s.map Char.toLower

/--
Replaces the first character in `s` with the result of applying `Char.toUpper` to it. Returns the
empty string if the string is empty.

`Char.toUpper` has no effect on characters outside of the range `'a'`–`'z'`.

Examples:
* `"orange".capitalize = "Orange"`
* `"ORANGE".capitalize = "ORANGE"`
* `"".capitalize = ""`
-/
@[inline] def capitalize (s : String) : String :=
  s.set 0 <| s.get 0 |>.toUpper

@[export lean_string_capitalize]
def Internal.capitalizeImpl (s : String) : String :=
  String.capitalize s

/--
Replaces the first character in `s` with the result of applying `Char.toLower` to it. Returns the
empty string if the string is empty.

`Char.toLower` has no effect on characters outside of the range `'A'`–`'Z'`.

Examples:
* `"Orange".decapitalize = "orange"`
* `"ORANGE".decapitalize = "oRANGE"`
* `"".decapitalize = ""`
-/
@[inline] def decapitalize (s : String) :=
  s.set 0 <| s.get 0 |>.toLower

/--
If `pre` is a prefix of `s`, returns the remainder. Returns `none` otherwise.

The string `pre` is a prefix of `s` if there exists a `t : String` such that `s = pre ++ t`. If so,
the result is `some t`.

Use `String.stripPrefix` to return the string unchanged when `pre` is not a prefix.

Examples:
 * `"red green blue".dropPrefix? "red " = some "green blue"`
 * `"red green blue".dropPrefix? "reed " = none`
 * `"red green blue".dropPrefix? "" = some "red green blue"`
-/
def dropPrefix? (s : String) (pre : String) : Option Substring :=
  s.toSubstring.dropPrefix? pre.toSubstring

/--
If `suff` is a suffix of `s`, returns the remainder. Returns `none` otherwise.

The string `suff` is a suffix of `s` if there exists a `t : String` such that `s = t ++ suff`. If so,
the result is `some t`.

Use `String.stripSuffix` to return the string unchanged when `suff` is not a suffix.

Examples:
 * `"red green blue".dropSuffix? " blue" = some "red green"`
 * `"red green blue".dropSuffix? " blu " = none`
 * `"red green blue".dropSuffix? "" = some "red green blue"`
-/
def dropSuffix? (s : String) (suff : String) : Option Substring :=
  s.toSubstring.dropSuffix? suff.toSubstring

/--
If `pre` is a prefix of `s`, returns the remainder. Returns `s` unmodified otherwise.

The string `pre` is a prefix of `s` if there exists a `t : String` such that `s = pre ++ t`. If so,
the result is `t`. Otherwise, it is `s`.

Use `String.dropPrefix?` to return `none` when `pre` is not a prefix.

Examples:
 * `"red green blue".stripPrefix "red " = "green blue"`
 * `"red green blue".stripPrefix "reed " = "red green blue"`
 * `"red green blue".stripPrefix "" = "red green blue"`
-/
def stripPrefix (s : String) (pre : String) : String :=
  s.dropPrefix? pre |>.map Substring.toString |>.getD s

/--
If `suff` is a suffix of `s`, returns the remainder. Returns `s` unmodified otherwise.

The string `suff` is a suffix of `s` if there exists a `t : String` such that `s = t ++ suff`. If so,
the result is `t`. Otherwise, it is `s`.

Use `String.dropSuffix?` to return `none` when `suff` is not a suffix.

Examples:
 * `"red green blue".stripSuffix " blue" = "red green"`
 * `"red green blue".stripSuffix " blu " = "red green blue"`
 * `"red green blue".stripSuffix "" = "red green blue"`
-/
def stripSuffix (s : String) (suff : String) : String :=
  s.dropSuffix? suff |>.map Substring.toString |>.getD s

end String

namespace String

@[ext]
theorem ext {s₁ s₂ : String} (h : s₁.data = s₂.data) : s₁ = s₂ :=
  data_injective h

@[simp] theorem default_eq : default = "" := rfl

@[simp]
theorem String.mk_eq_asString (s : List Char) : String.mk s = List.asString s := rfl

@[simp] theorem length_empty : "".length = 0 := by simp [← length_data, data_empty]

theorem singleton_eq {c : Char} : String.singleton c = [c].asString := by
  simp [← bytes_inj]

@[simp] theorem data_singleton (c : Char) : (String.singleton c).data = [c] := by
  simp [singleton_eq]

@[simp]
theorem length_singleton {c : Char} : (String.singleton c).length = 1 := by
  simp [← length_data]

theorem push_eq_append (c : Char) : String.push s c = s ++ singleton c := by
  simp

@[simp] theorem data_push (c : Char) : (String.push s c).data = s.data ++ [c] := by
  simp [← append_singleton]

@[simp] theorem length_push (c : Char) : (String.push s c).length = s.length + 1 := by
  simp [← length_data]

@[simp] theorem length_pushn (c : Char) (n : Nat) : (pushn s c n).length = s.length + n := by
  unfold pushn; induction n <;> simp [Nat.repeat, Nat.add_assoc, *]

@[simp] theorem length_append (s t : String) : (s ++ t).length = s.length + t.length := by
  simp [← length_data]

attribute [simp] toList -- prefer `String.data` over `String.toList` in lemmas

theorem lt_iff {s t : String} : s < t ↔ s.data < t.data := .rfl

namespace Pos

theorem byteIdx_mk (n : Nat) : byteIdx ⟨n⟩ = n := rfl

@[simp] theorem mk_zero : ⟨0⟩ = (0 : Pos) := rfl

@[simp] theorem mk_byteIdx (p : Pos) : ⟨p.byteIdx⟩ = p := rfl

@[simp] theorem add_byteIdx (p₁ p₂ : Pos) : (p₁ + p₂).byteIdx = p₁.byteIdx + p₂.byteIdx := rfl

theorem add_eq (p₁ p₂ : Pos) : p₁ + p₂ = ⟨p₁.byteIdx + p₂.byteIdx⟩ := rfl

@[simp] theorem sub_byteIdx (p₁ p₂ : Pos) : (p₁ - p₂).byteIdx = p₁.byteIdx - p₂.byteIdx := rfl

theorem sub_eq (p₁ p₂ : Pos) : p₁ - p₂ = ⟨p₁.byteIdx - p₂.byteIdx⟩ := rfl

@[simp] theorem addChar_byteIdx (p : Pos) (c : Char) : (p + c).byteIdx = p.byteIdx + c.utf8Size := rfl

theorem addChar_eq (p : Pos) (c : Char) : p + c = ⟨p.byteIdx + c.utf8Size⟩ := rfl

theorem zero_addChar_byteIdx (c : Char) : ((0 : Pos) + c).byteIdx = c.utf8Size := by
  simp only [addChar_byteIdx, byteIdx_zero, Nat.zero_add]

theorem zero_addChar_eq (c : Char) : (0 : Pos) + c = ⟨c.utf8Size⟩ := by rw [← zero_addChar_byteIdx]

theorem addChar_right_comm (p : Pos) (c₁ c₂ : Char) : p + c₁ + c₂ = p + c₂ + c₁ := by
  apply Pos.ext
  repeat rw [pos_add_char]
  apply Nat.add_right_comm

theorem ne_of_gt {i₁ i₂ : Pos} (h : i₁ < i₂) : i₂ ≠ i₁ := (ne_of_lt h).symm

@[simp] theorem byteIdx_addString (p : Pos) (s : String) :
    (p + s).byteIdx = p.byteIdx + s.utf8ByteSize := rfl

@[deprecated byteIdx_addString (since := "2025-03-18")]
abbrev addString_byteIdx := @byteIdx_addString

theorem addString_eq (p : Pos) (s : String) : p + s = ⟨p.byteIdx + s.utf8ByteSize⟩ := rfl

theorem byteIdx_zero_addString (s : String) : ((0 : Pos) + s).byteIdx = s.utf8ByteSize := by
  simp only [byteIdx_addString, byteIdx_zero, Nat.zero_add]

@[deprecated byteIdx_zero_addString (since := "2025-03-18")]
abbrev zero_addString_byteIdx := @byteIdx_zero_addString

theorem zero_addString_eq (s : String) : (0 : Pos) + s = ⟨s.utf8ByteSize⟩ := by
  rw [← byteIdx_zero_addString]

@[simp] theorem mk_le_mk {i₁ i₂ : Nat} : Pos.mk i₁ ≤ Pos.mk i₂ ↔ i₁ ≤ i₂ := .rfl

@[simp] theorem le_refl {p : Pos} : p ≤ p := mk_le_mk.mpr (Nat.le_refl _)

@[simp] theorem mk_lt_mk {i₁ i₂ : Nat} : Pos.mk i₁ < Pos.mk i₂ ↔ i₁ < i₂ := .rfl

end Pos

@[simp] theorem get!_eq_get (s : String) (p : Pos) : get! s p = get s p := rfl

theorem lt_next' (s : String) (p : Pos) : p < next s p := lt_next ..

@[simp] theorem prev_zero (s : String) : prev s 0 = 0 := by
  rw [prev]
  cases s.data <;> simp [utf8PrevAux, Pos.le_iff]

@[simp] theorem get'_eq (s : String) (p : Pos) (h) : get' s p h = get s p := rfl

@[simp] theorem next'_eq (s : String) (p : Pos) (h) : next' s p h = next s p := rfl

-- `toSubstring'` is just a synonym for `toSubstring` without the `@[inline]` attribute
-- so for proving can be unfolded.
attribute [simp] toSubstring'

end String

namespace Char

theorem toString_eq_singleton {c : Char} : c.toString = String.singleton c := rfl

@[simp] theorem length_toString (c : Char) : c.toString.length = 1 := by
  simp [toString_eq_singleton]

end Char

open String

namespace Substring

@[simp] theorem prev_zero (s : Substring) : s.prev 0 = 0 := by simp [prev, Pos.add_eq, Pos.byteIdx_zero]

@[simp] theorem prevn_zero (s : Substring) : ∀ n, s.prevn n 0 = 0
  | 0 => rfl
  | n+1 => by simp [prevn, prevn_zero s n]

end Substring
