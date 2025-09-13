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

public section

universe u

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
Returns the length of a string in Unicode code points.

Examples:
* `"".length = 0`
* `"abc".length = 3`
* `"L∃∀N".length = 4`
-/
@[extern "lean_string_length", expose]
def length : (@& String) → Nat
  | ⟨s⟩ => s.length

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

/--
Converts a string to a list of characters.

Even though the logical model of strings is as a structure that wraps a list of characters, this
operation takes time and space linear in the length of the string. At runtime, strings are
represented as dynamic arrays of bytes.

Examples:
 * `"abc".toList = ['a', 'b', 'c']`
 * `"".toList = []`
 * `"\n".toList = ['\n']`
-/
@[expose] def toList (s : String) : List Char :=
  s.data

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
@[extern "lean_string_is_valid_pos"]
def Pos.isValid (s : @&String) (p : @& Pos) : Bool :=
  go s.data 0
where
  go : List Char → Pos → Bool
  | [],    i => i = p
  | c::cs, i => if i = p then true else go cs (i + c)

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
@[extern "lean_string_utf8_get_opt"]
def get? : (@& String) → (@& Pos) → Option Char
  | ⟨s⟩, p => utf8GetAux? s 0 p

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
  | ⟨s⟩ => utf8GetAux s 0 p

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
Replaces the character at position `p` in the string `s` with the result of applying `f` to that
character. If `p` is an invalid position, the string is returned unchanged.

If both the replacement character and the replaced character are 7-bit ASCII characters and the
string is not shared, then it is updated in-place and not copied.

Examples:
* `"abc".modify ⟨1⟩ Char.toUpper = "aBc"`
* `"abc".modify ⟨3⟩ Char.toUpper = "abc"`
-/
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
Returns the first character in `s`. If `s = ""`, returns `(default : Char)`.

Examples:
* `"abc".front = 'a'`
* `"".front = (default : Char)`
-/
@[inline] def front (s : String) : Char :=
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
@[inline] def back (s : String) : Char :=
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
  | ⟨s⟩ => utf8GetAux s 0 p

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

theorem _root_.Char.utf8Size_pos (c : Char) : 0 < c.utf8Size := by
  repeat first | apply iteInduction (motive := (0 < ·)) <;> intros | decide

theorem _root_.Char.utf8Size_le_four (c : Char) : c.utf8Size ≤ 4 := by
  repeat first | apply iteInduction (motive := (· ≤ 4)) <;> intros | decide

theorem _root_.Char.utf8Size_eq (c : Char) : c.utf8Size = 1 ∨ c.utf8Size = 2 ∨ c.utf8Size = 3 ∨ c.utf8Size = 4 := by
  match c.utf8Size, c.utf8Size_pos, c.utf8Size_le_four with
  | 1, _, _ | 2, _, _ | 3, _, _ | 4, _, _ => simp

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
def extract : (@& String) → (@& Pos) → (@& Pos) → String
  | ⟨s⟩, b, e => if b.byteIdx ≥ e.byteIdx then "" else ⟨go₁ s 0 b e⟩
where
  go₁ : List Char → Pos → Pos → Pos → List Char
    | [],        _, _, _ => []
    | s@(c::cs), i, b, e => if i = b then go₂ s i e else go₁ cs (i + c) b e

  go₂ : List Char → Pos → Pos → List Char
    | [],    _, _ => []
    | c::cs, i, e => if i = e then [] else c :: go₂ cs (i + c) e


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
  all_goals simp_wf
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
  simp [next, get, set, endPos, utf8ByteSize] at h ⊢
  rw [Nat.add_comm i.1, Nat.add_assoc] at h ⊢
  let rec foo : ∀ cs a b₁ b₂,
    (utf8GetAux cs a i).utf8Size + b₁ = utf8ByteSize.go cs + b₂ →
    (utf8GetAux (utf8SetAux c cs a i) a i).utf8Size + b₁ = utf8ByteSize.go (utf8SetAux c cs a i) + b₂
  | [], _, _, _, h => h
  | c'::cs, a, b₁, b₂, h => by
    unfold utf8SetAux
    apply iteInduction (motive := fun p => (utf8GetAux p a i).utf8Size + b₁ = utf8ByteSize.go p + b₂) <;>
      intro h' <;> simp [utf8GetAux, h', utf8ByteSize.go] at h ⊢
    next =>
      rw [Nat.add_assoc, Nat.add_left_comm] at h ⊢; rw [Nat.add_left_cancel h]
    next =>
      rw [Nat.add_assoc] at h ⊢
      refine foo cs (a + c') b₁ (c'.utf8Size + b₂) h
  exact foo s.1 0 _ _ h

theorem mapAux_lemma (s : String) (i : Pos) (c : Char) (h : ¬s.atEnd i) :
    (s.set i c).endPos.1 - ((s.set i c).next i).1 < s.endPos.1 - i.1 :=
  suffices (s.set i c).endPos.1 - ((s.set i c).next i).1 = s.endPos.1 - (s.next i).1 by
    rw [this]
    apply Nat.sub_lt_sub_left (Nat.gt_of_not_le (mt decide_eq_true h)) (lt_next ..)
  Nat.sub.elim (motive := (_ = ·)) _ _
    (fun _ k e =>
      have := set_next_add _ _ _ k 0 e.symm
      Nat.sub_eq_of_eq_add <| this.symm.trans <| Nat.add_comm ..)
    (fun h => by
      have ⟨k, e⟩ := Nat.le.dest h
      rw [Nat.succ_add] at e
      have : ((s.set i c).next i).1 = _ := set_next_add _ _ c 0 k.succ e.symm
      exact Nat.sub_eq_zero_of_le (this ▸ Nat.le_add_right ..))

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
@[inline] def front (s : Substring) : Char :=
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

theorem lt_iff {s t : String} : s < t ↔ s.data < t.data := .rfl

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

@[simp] theorem addChar_byteIdx (p : Pos) (c : Char) : (p + c).byteIdx = p.byteIdx + c.utf8Size := rfl

theorem addChar_eq (p : Pos) (c : Char) : p + c = ⟨p.byteIdx + c.utf8Size⟩ := rfl

theorem zero_addChar_byteIdx (c : Char) : ((0 : Pos) + c).byteIdx = c.utf8Size := by
  simp only [addChar_byteIdx, byteIdx_zero, Nat.zero_add]

theorem zero_addChar_eq (c : Char) : (0 : Pos) + c = ⟨c.utf8Size⟩ := by rw [← zero_addChar_byteIdx]

theorem addChar_right_comm (p : Pos) (c₁ c₂ : Char) : p + c₁ + c₂ = p + c₂ + c₁ := by
  apply ext
  repeat rw [pos_add_char]
  apply Nat.add_right_comm

theorem ne_of_lt {i₁ i₂ : Pos} (h : i₁ < i₂) : i₁ ≠ i₂ := mt ext_iff.1 (Nat.ne_of_lt h)

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

theorem le_iff {i₁ i₂ : Pos} : i₁ ≤ i₂ ↔ i₁.byteIdx ≤ i₂.byteIdx := .rfl

@[simp] theorem mk_le_mk {i₁ i₂ : Nat} : Pos.mk i₁ ≤ Pos.mk i₂ ↔ i₁ ≤ i₂ := .rfl

@[simp] theorem le_refl {p : Pos} : p ≤ p := mk_le_mk.mpr (Nat.le_refl _)

@[simp] theorem le_trans {p1 p2 p3 : Pos} : p1 ≤ p2 → p2 ≤ p3 → p1 ≤ p3 := fun h1 h2 =>
  mk_le_mk.mpr <| Nat.le_trans (mk_le_mk.mp h1) (mk_le_mk.mp h2)

theorem lt_iff {i₁ i₂ : Pos} : i₁ < i₂ ↔ i₁.byteIdx < i₂.byteIdx := .rfl

@[simp] theorem mk_lt_mk {i₁ i₂ : Nat} : Pos.mk i₁ < Pos.mk i₂ ↔ i₁ < i₂ := .rfl

end Pos

@[simp] theorem get!_eq_get (s : String) (p : Pos) : get! s p = get s p := rfl

theorem lt_next' (s : String) (p : Pos) : p < next s p := lt_next ..

@[simp] theorem prev_zero (s : String) : prev s 0 = 0 := by
  cases s with | mk cs
  cases cs
  next => rfl
  next => simp [prev, utf8PrevAux, Pos.le_iff]

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
