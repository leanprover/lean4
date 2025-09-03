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
opaque foldl {α : Type u} [Inhabited α] (f : α → Char → α) (init : α) (s : String) : α

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

/-

/--
Creates a string that contains the characters in a list, in order.

Examples:
 * `['L', '∃', '∀', 'N'].asString = "L∃∀N"`
 * `[].asString = ""`
 * `['a', 'a', 'a'].asString = "aaa"`
-/
def List.asString (s : List Char) : String :=
  ⟨s⟩

namespace String

instance : HAdd String.Pos String.Pos String.Pos where
  hAdd p₁ p₂ := { byteIdx := p₁.byteIdx + p₂.byteIdx }

instance : HAdd String.Pos Char String.Pos where
  hAdd p c := { byteIdx := p.byteIdx + c.utf8Size }

instance : HSub String.Pos String.Pos String.Pos where
  hSub p₁ p₂ := { byteIdx :=  p₁.byteIdx - p₂.byteIdx }

instance : LE String.Pos where
  le p₁ p₂ := p₁.byteIdx ≤ p₂.byteIdx

instance : LT String.Pos where
  lt p₁ p₂ := p₁.byteIdx < p₂.byteIdx

instance (p₁ p₂ : String.Pos) : Decidable (LE.le p₁ p₂) :=
  inferInstanceAs (Decidable (p₁.byteIdx ≤ p₂.byteIdx))

instance (p₁ p₂ : String.Pos) : Decidable (LT.lt p₁ p₂) :=
  inferInstanceAs (Decidable (p₁.byteIdx < p₂.byteIdx))

instance : Min String.Pos := minOfLe

instance : OfNat String.Pos (nat_lit 0) where
  ofNat := {}

/--
Returns the length of a string in Unicode code points.

Examples:
* `"".length = 0`
* `"abc".length = 3`
* `"L∃∀N".length = 4`
-/
@[extern "lean_string_length", expose]
def length : (@& String) → Nat
  | ⟨s⟩ => s.length

theorem _root_.Char.utf8Size_pos (c : Char) : 0 < c.utf8Size := by
  repeat first | apply iteInduction (motive := (0 < ·)) <;> intros | decide

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
  match s with
  | ⟨s⟩ => utf8GetAux s 0 p

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

theorem lt_next (s : String) (i : Pos) : i.1 < (s.next i).1 :=
  Nat.add_lt_add_left (Char.utf8Size_pos _) _

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
def extract : (@& String) → (@& Pos) → (@& Pos) → String
  | ⟨s⟩, b, e => if b.byteIdx ≥ e.byteIdx then "" else ⟨go₁ s 0 b e⟩
where
  go₁ : List Char → Pos → Pos → Pos → List Char
    | [],        _, _, _ => []
    | s@(c::cs), i, b, e => if i = b then go₂ s i e else go₁ cs (i + c) b e

  go₂ : List Char → Pos → Pos → List Char
    | [],    _, _ => []
    | c::cs, i, e => if i = e then [] else c :: go₂ cs (i + c) e

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
  | ⟨s⟩, c => ⟨s ++ [c]⟩

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

/--
Returns a new string that contains only the character `c`.

Because strings are encoded in UTF-8, the resulting string may take multiple bytes.

Examples:
 * `String.singleton 'L' = "L"`
 * `String.singleton ' ' = " "`
 * `String.singleton '"' = "\""`
 * `String.singleton '𝒫' = "𝒫"`
-/
@[inline,expose] def singleton (c : Char) : String :=
  "".push c

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

/--
Appends two strings. Usually accessed via the `++` operator.

The internal implementation will perform destructive updates if the string is not shared.

Examples:
 * `"abc".append "def" = "abcdef"`
 * `"abc" ++ "def" = "abcdef"`
 * `"" ++ "" = ""`
-/
@[extern "lean_string_append", expose]
def append : String → (@& String) → String
  | ⟨a⟩, ⟨b⟩ => ⟨a ++ b⟩

instance : Append String := ⟨String.append⟩

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

/--
Checks whether a string contains the specified character.

Examples:
* `"green".contains 'e' = true`
* `"green".contains 'x' = false`
* `"".contains 'x' = false`
-/
@[inline] def contains (s : String) (c : Char) : Bool :=
s.any (fun a => a == c)

instance : Inhabited String := ⟨""⟩

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
@[extern "lean_string_utf8_set"]
def set : String → (@& Pos) → Char → String
  | ⟨s⟩, i, c => ⟨utf8SetAux c s 0 i⟩

/--
Replaces the first character in `s` with the result of applying `Char.toUpper` to it. Returns the
empty string if the string is empty.

`Char.toUpper` has no effect on characters outside of the range `'a'`–`'z'`.

Examples:
* `"orange".capitalize = "Orange"`
* `"ORANGE".capitalize = "ORANGE"`
* `"".capitalize = ""`
-/
@[inline] def capitalize (s : String) :=
  s.set 0 <| s.get 0 |>.toUpper

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
  | ⟨s⟩, p => utf8PrevAux s 0 p

/--
Returns either `p₁` or `p₂`, whichever has the least byte index.
-/
abbrev Pos.min (p₁ p₂ : Pos) : Pos :=
  { byteIdx := p₁.byteIdx.min p₂.byteIdx }

/--
Returns the first character in `s`. If `s = ""`, returns `(default : Char)`.

Examples:
* `"abc".front = 'a'`
* `"".front = (default : Char)`
-/
@[inline] def front (s : String) : Char :=
  get s 0

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

end String

namespace Substring

/--
Copies the region of the underlying string pointed to by a substring into a fresh string.
-/
@[inline] def toString : Substring → String
  | ⟨s, b, e⟩ => s.extract b e

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
Removes the specified number of characters (Unicode code points) from the beginning of a substring
by advancing its start position.

If the substring's end position is reached, the start position is not advanced past it.
-/
@[inline] def drop : Substring → Nat → Substring
  | ss@⟨s, b, e⟩, n => ⟨s, b + ss.nextn n 0, e⟩

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

/--
Checks whether two substrings represent equal strings. Usually accessed via the `==` operator.

Two substrings do not need to have the same underlying string or the same start and end positions;
instead, they are equal if they contain the same sequence of characters.
-/
def beq (ss1 ss2 : Substring) : Bool :=
  ss1.bsize == ss2.bsize && ss1.str.substrEq ss1.startPos ss2.str ss2.startPos ss1.bsize

instance hasBeq : BEq Substring := ⟨beq⟩

/--
Returns the character at the given position in the substring.

The position is relative to the substring, rather than the underlying string, and no bounds checking
is performed with respect to the substring's end position. If the relative position is not a valid
position in the underlying string, the fallback value `(default : Char)`, which is `'A'`, is
returned.  Does not panic.
-/
@[inline] def get : Substring → String.Pos → Char
  | ⟨s, b, _⟩, p => s.get (b+p)

/--
Returns the first character in the substring.

If the substring is empty, but the substring's start position is a valid position in the underlying
string, then the character at the start position is returned. If the substring's start position is
not a valid position in the string, the fallback value `(default : Char)`, which is `'A'`, is
returned.  Does not panic.
-/
@[inline] def front (s : Substring) : Char :=
  s.get 0

@[specialize] def takeWhileAux (s : String) (stopPos : String.Pos) (p : Char → Bool) (i : String.Pos) : String.Pos :=
  if h : i < stopPos then
    if p (s.get i) then
      have := Nat.sub_lt_sub_left h (String.lt_next s i)
      takeWhileAux s stopPos p (s.next i)
    else i
  else i
termination_by stopPos.1 - i.1

/--
Checks whether a substring is empty.

A substring is empty if its start and end positions are the same.
-/
@[inline] def isEmpty (ss : Substring) : Bool :=
  ss.bsize == 0

/--
Retains only the longest prefix of a substring in which a Boolean predicate returns `true` for all
characters by moving the substring's end position towards its start position.
-/
@[inline] def takeWhile : Substring → (Char → Bool) → Substring
  | ⟨s, b, e⟩, p =>
    let e := takeWhileAux s e p b;
    ⟨s, b, e⟩

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
Returns the position that's the specified number of characters prior to the given position in a
substring. If the start position of the substring is reached, it is returned.

Both the input position and the returned position are interpreted relative to the substring's start
position, not the underlying string.
-/
def prevn : Substring → Nat → String.Pos → String.Pos
  | _,  0,   p => p
  | ss, i+1, p => ss.prevn i (ss.prev p)

/--
Removes the specified number of characters (Unicode code points) from the end of a substring
by moving its end position towards its start position.

If the substring's start position is reached, the end position is not retracted past it.
-/
@[inline] def dropRight : Substring → Nat → Substring
  | ss@⟨s, b, _⟩, n => ⟨s, b, b + ss.prevn n ⟨ss.bsize⟩⟩

end Substring

namespace String

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

end String

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
-/
