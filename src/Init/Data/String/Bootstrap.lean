/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Mario Carneiro
-/
module

prelude
public import Init.Data.List.Basic
public import Init.Data.Char.Basic

public section

namespace String

instance : OfNat String.Pos (nat_lit 0) where
  ofNat := {}

instance : Inhabited String where
  default := ""

end String

namespace String.Internal

@[extern "lean_string_posof"]
opaque posOf (s : String) (c : Char) : Pos

@[extern "lean_string_offsetofpos"]
opaque offsetOfPos (s : String) (pos : Pos) : Nat

@[extern "lean_string_utf8_extract"]
opaque extract : (@& String) → (@& Pos) → (@& Pos) → String

@[extern "lean_string_length"]
opaque length : (@& String) → Nat

@[extern "lean_string_push"]
opaque push : String → Char → String

@[extern "lean_string_pushn"]
opaque pushn (s : String) (c : Char) (n : Nat) : String

@[extern "lean_string_append"]
opaque append : String → (@& String) → String

@[extern "lean_string_utf8_next"]
opaque next (s : @& String) (p : @& Pos) : Pos

@[extern "lean_string_isempty"]
opaque isEmpty (s : String) : Bool

@[extern "lean_string_foldl"]
opaque foldl (f : String → Char → String) (init : String) (s : String) : String

@[extern "lean_string_singleton"]
opaque singleton (c : Char) : String

@[extern "lean_string_isprefixof"]
opaque isPrefixOf (p : String) (s : String) : Bool

@[extern "lean_string_any"]
opaque any (s : String) (p : Char → Bool) : Bool

@[extern "lean_string_contains"]
opaque contains (s : String) (c : Char) : Bool

@[extern "lean_string_utf8_get"]
opaque get (s : @& String) (p : @& Pos) : Char

@[extern "lean_string_capitalize"]
opaque capitalize (s : String) : String

@[extern "lean_string_utf8_at_end"]
opaque atEnd : (@& String) → (@& Pos) → Bool

@[extern "lean_string_nextwhile"]
opaque nextWhile (s : String) (p : Char → Bool) (i : String.Pos) : String.Pos

@[extern "lean_string_trim"]
opaque trim (s : String) : String

@[extern "lean_string_intercalate"]
opaque intercalate (s : String) : List String → String

@[extern "lean_string_front"]
opaque front (s : String) : Char

@[extern "lean_string_drop"]
opaque drop (s : String) (n : Nat) : String

@[extern "lean_string_dropright"]
opaque dropRight (s : String) (n : Nat) : String

end String.Internal

@[extern "lean_list_asstring"]
opaque List.Internal.asString (s : List Char) : String

namespace Substring.Internal

@[extern "lean_substring_tostring"]
opaque toString : Substring → String

@[extern "lean_substring_drop"]
opaque drop : Substring → Nat → Substring

@[extern "lean_substring_front"]
opaque front (s : Substring) : Char

@[extern "lean_substring_takewhile"]
opaque takeWhile : Substring → (Char → Bool) → Substring

@[extern "lean_substring_extract"]
opaque extract : Substring → String.Pos → String.Pos → Substring

@[extern "lean_substring_all"]
opaque all (s : Substring) (p : Char → Bool) : Bool

@[extern "lean_substring_beq"]
opaque beq (ss1 ss2 : Substring) : Bool

@[extern "lean_substring_isempty"]
opaque isEmpty (ss : Substring) : Bool

@[extern "lean_substring_get"]
opaque get : Substring → String.Pos → Char

@[extern "lean_substring_prev"]
opaque prev : Substring → String.Pos → String.Pos

end Substring.Internal

namespace String.Pos.Internal

@[extern "lean_string_pos_sub"]
opaque sub : String.Pos → String.Pos → String.Pos

@[extern "lean_string_pos_min"]
opaque min (p₁ p₂ : Pos) : Pos

end String.Pos.Internal

namespace Char.Internal

@[extern "lean_char_tostring"]
opaque toString (c : Char) : String

end Char.Internal
