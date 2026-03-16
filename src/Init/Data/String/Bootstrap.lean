/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Mario Carneiro
-/
module

prelude
public import Init.Data.ByteArray.Bootstrap
import Init.Data.Char.Basic

public section

namespace String

instance : OfNat String.Pos.Raw (nat_lit 0) where
  ofNat := {}

instance : Inhabited String where
  default := ""

/--
Adds a character to the end of a string.

The internal implementation uses dynamic arrays and will perform destructive updates
if the string is not shared.

Examples:
* `"abc".push 'd' = "abcd"`
* `"".push 'a' = "a"`
-/
@[extern "lean_string_push", expose]
def push : String → Char → String
  | ⟨b, h⟩, c => ⟨b.append (List.utf8Encode [c]), ?pf⟩
where finally
  have ⟨m, hm⟩ := h
  cases hm
  exact .intro (m ++ [c]) (by simp [List.utf8Encode, List.toByteArray_append'])

/--
Returns a new string that contains only the character `c`.

Because strings are encoded in UTF-8, the resulting string may take multiple bytes.

Examples:
 * `String.singleton 'L' = "L"`
 * `String.singleton ' ' = " "`
 * `String.singleton '"' = "\""`
 * `String.singleton '𝒫' = "𝒫"`
-/
@[inline, expose] def singleton (c : Char) : String :=
  "".push c

end String

namespace String.Internal

set_option compiler.ignoreBorrowAnnotation true in
@[extern "lean_string_posof"]
opaque posOf (s : String) (c : Char) : Pos.Raw

set_option compiler.ignoreBorrowAnnotation true in
@[extern "lean_string_offsetofpos"]
opaque offsetOfPos (s : String) (pos : Pos.Raw) : Nat

@[extern "lean_string_utf8_extract"]
opaque extract : (@& String) → (@& Pos.Raw) → (@& Pos.Raw) → String

@[extern "lean_string_length"]
opaque length : (@& String) → Nat

set_option compiler.ignoreBorrowAnnotation true in
@[extern "lean_string_pushn"]
opaque pushn (s : String) (c : Char) (n : Nat) : String

@[extern "lean_string_append"]
opaque append : String → (@& String) → String

@[extern "lean_string_utf8_next"]
opaque next (s : @& String) (p : @& Pos.Raw) : Pos.Raw

set_option compiler.ignoreBorrowAnnotation true in
@[extern "lean_string_isempty"]
opaque isEmpty (s : String) : Bool

set_option compiler.ignoreBorrowAnnotation true in
@[extern "lean_string_foldl"]
opaque foldl (f : String → Char → String) (init : String) (s : String) : String

set_option compiler.ignoreBorrowAnnotation true in
@[extern "lean_string_isprefixof"]
opaque isPrefixOf (p : String) (s : String) : Bool

set_option compiler.ignoreBorrowAnnotation true in
@[extern "lean_string_any"]
opaque any (s : String) (p : Char → Bool) : Bool

set_option compiler.ignoreBorrowAnnotation true in
@[extern "lean_string_contains"]
opaque contains (s : String) (c : Char) : Bool

@[extern "lean_string_utf8_get"]
opaque get (s : @& String) (p : @& Pos.Raw) : Char

set_option compiler.ignoreBorrowAnnotation true in
@[extern "lean_string_capitalize"]
opaque capitalize (s : String) : String

@[extern "lean_string_utf8_at_end"]
opaque atEnd : (@& String) → (@& Pos.Raw) → Bool

set_option compiler.ignoreBorrowAnnotation true in
@[extern "lean_string_nextwhile"]
opaque nextWhile (s : String) (p : Char → Bool) (i : String.Pos.Raw) : String.Pos.Raw

set_option compiler.ignoreBorrowAnnotation true in
@[extern "lean_string_trim"]
opaque trim (s : String) : String

set_option compiler.ignoreBorrowAnnotation true in
@[extern "lean_string_intercalate"]
opaque intercalate (s : String) : List String → String

set_option compiler.ignoreBorrowAnnotation true in
@[extern "lean_string_front"]
opaque front (s : String) : Char

set_option compiler.ignoreBorrowAnnotation true in
@[extern "lean_string_drop"]
opaque drop (s : String) (n : Nat) : String

set_option compiler.ignoreBorrowAnnotation true in
@[extern "lean_string_dropright"]
opaque dropRight (s : String) (n : Nat) : String

@[extern "lean_string_get_byte_fast"]
opaque getUTF8Byte (s : @& String) (n : Nat) (h : n < s.utf8ByteSize) : UInt8

end String.Internal

@[extern "lean_string_mk", expose, deprecated String.ofList (since := "2025-10-30")]
def String.mk (data : List Char) : String :=
  ⟨List.utf8Encode data,.intro data rfl⟩

/--
Creates a string that contains the characters in a list, in order.

Examples:
 * `['L', '∃', '∀', 'N'].asString = "L∃∀N"`
 * `[].asString = ""`
 * `['a', 'a', 'a'].asString = "aaa"`
-/
@[expose, inline, deprecated String.ofList (since := "2025-10-30")]
def List.asString (s : List Char) : String :=
  String.ofList s

namespace Substring.Raw.Internal

set_option compiler.ignoreBorrowAnnotation true in
@[extern "lean_substring_tostring"]
opaque toString : Substring.Raw → String

set_option compiler.ignoreBorrowAnnotation true in
@[extern "lean_substring_drop"]
opaque drop : Substring.Raw → Nat → Substring.Raw

set_option compiler.ignoreBorrowAnnotation true in
@[extern "lean_substring_front"]
opaque front (s : Substring.Raw) : Char

set_option compiler.ignoreBorrowAnnotation true in
@[extern "lean_substring_takewhile"]
opaque takeWhile : Substring.Raw → (Char → Bool) → Substring.Raw

set_option compiler.ignoreBorrowAnnotation true in
@[extern "lean_substring_extract"]
opaque extract : Substring.Raw → String.Pos.Raw → String.Pos.Raw → Substring.Raw

set_option compiler.ignoreBorrowAnnotation true in
@[extern "lean_substring_all"]
opaque all (s : Substring.Raw) (p : Char → Bool) : Bool

set_option compiler.ignoreBorrowAnnotation true in
@[extern "lean_substring_beq"]
opaque beq (ss1 ss2 : Substring.Raw) : Bool

set_option compiler.ignoreBorrowAnnotation true in
@[extern "lean_substring_isempty"]
opaque isEmpty (ss : Substring.Raw) : Bool

set_option compiler.ignoreBorrowAnnotation true in
@[extern "lean_substring_get"]
opaque get : Substring.Raw → String.Pos.Raw → Char

set_option compiler.ignoreBorrowAnnotation true in
@[extern "lean_substring_prev"]
opaque prev : Substring.Raw → String.Pos.Raw → String.Pos.Raw

end Substring.Raw.Internal

namespace String.Pos.Raw.Internal

set_option compiler.ignoreBorrowAnnotation true in
@[extern "lean_string_pos_sub"]
opaque sub : String.Pos.Raw → String.Pos.Raw → String.Pos.Raw

set_option compiler.ignoreBorrowAnnotation true in
@[extern "lean_string_pos_min"]
opaque min (p₁ p₂ : Pos.Raw) : Pos.Raw

end String.Pos.Raw.Internal

namespace Char

/--
Constructs a singleton string that contains only the provided character.

Examples:
 * `'L'.toString = "L"`
 * `'"'.toString = "\""`
-/
@[inline, expose] protected def toString (c : Char) : String :=
  String.singleton c

end Char
