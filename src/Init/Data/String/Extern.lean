/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Data.List.Basic
import Init.Data.Char.Basic
import Init.Data.Option.Basic

universe u

namespace String

instance : OfNat String.Pos (nat_lit 0) where
  ofNat := {}

instance : LT String :=
  ⟨fun s₁ s₂ => s₁.data < s₂.data⟩

@[extern "lean_string_dec_lt"]
instance decLt (s₁ s₂ : @& String) : Decidable (s₁ < s₂) :=
  List.hasDecidableLt s₁.data s₂.data

/--
Returns the length of a string in Unicode code points.

Examples:
* `"".length = 0`
* `"abc".length = 3`
* `"L∃∀N".length = 4`
-/
@[extern "lean_string_length"]
def length : (@& String) → Nat
  | ⟨s⟩ => s.length

/--
Pushes a character onto the end of a string.

The internal implementation uses dynamic arrays and will perform destructive updates
if the string is not shared.

Example: `"abc".push 'd' = "abcd"`
-/
@[extern "lean_string_push"]
def push : String → Char → String
  | ⟨s⟩, c => ⟨s ++ [c]⟩

/--
Appends two strings.

The internal implementation uses dynamic arrays and will perform destructive updates
if the string is not shared.

Example: `"abc".append "def" = "abcdef"`
-/
@[extern "lean_string_append"]
def append : String → (@& String) → String
  | ⟨a⟩, ⟨b⟩ => ⟨a ++ b⟩

/-- Returns true if `p` is a valid UTF-8 position in the string `s`, meaning that `p ≤ s.endPos`
and `p` lies on a UTF-8 character boundary. This has an O(1) implementation in the runtime. -/
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
Returns the character at position `p` of a string. If `p` is not a valid position,
returns `(default : Char)`.

See `utf8GetAux` for the reference implementation.

Examples:
* `"abc".get ⟨1⟩ = 'b'`
* `"abc".get ⟨3⟩ = (default : Char) = 'A'`

Positions can also be invalid if a byte index points into the middle of a multi-byte UTF-8
character. For example,`"L∃∀N".get ⟨2⟩ = (default : Char) = 'A'`.
-/
@[extern "lean_string_utf8_get"]
def get (s : @& String) (p : @& Pos) : Char :=
  match s with
  | ⟨s⟩ => utf8GetAux s 0 p

def utf8GetAux? : List Char → Pos → Pos → Option Char
  | [],    _, _ => none
  | c::cs, i, p => if i = p then c else utf8GetAux? cs (i + c) p

/--
Returns the character at position `p`. If `p` is not a valid position, returns `none`.

Examples:
* `"abc".get? ⟨1⟩ = some 'b'`
* `"abc".get? ⟨3⟩ = none`

Positions can also be invalid if a byte index points into the middle of a multi-byte UTF-8
character. For example, `"L∃∀N".get? ⟨2⟩ = none`
-/
@[extern "lean_string_utf8_get_opt"]
def get? : (@& String) → (@& Pos) → Option Char
  | ⟨s⟩, p => utf8GetAux? s 0 p

/--
Returns the character at position `p` of a string. If `p` is not a valid position,
returns `(default : Char)` and produces a panic error message.

Examples:
* `"abc".get! ⟨1⟩ = 'b'`
* `"abc".get! ⟨3⟩` panics

Positions can also be invalid if a byte index points into the middle of a multi-byte UTF-8 character. For example,
`"L∃∀N".get! ⟨2⟩` panics.
-/
-- @[extern "lean_string_utf8_get_bang"]
-- def get! (s : @& String) (p : @& Pos) : Char :=
--   match s with
--   | ⟨s⟩ => utf8GetAux s 0 p

def utf8SetAux (c' : Char) : List Char → Pos → Pos → List Char
  | [],    _, _ => []
  | c::cs, i, p =>
    if i = p then (c'::cs) else c::(utf8SetAux c' cs (i + c) p)

/--
Replaces the character at a specified position in a string with a new character. If the position
is invalid, the string is returned unchanged.

If both the replacement character and the replaced character are ASCII characters and the string
is not shared, destructive updates are used.

Examples:
* `"abc".set ⟨1⟩ 'B' = "aBc"`
* `"abc".set ⟨3⟩ 'D' = "abc"`
* `"L∃∀N".set ⟨4⟩ 'X' = "L∃XN"`

Because `'∃'` is a multi-byte character, the byte index `2` in `L∃∀N` is an invalid position,
so `"L∃∀N".set ⟨2⟩ 'X' = "L∃∀N"`.
-/
@[extern "lean_string_utf8_set"]
def set : String → (@& Pos) → Char → String
  | ⟨s⟩, i, c => ⟨utf8SetAux c s 0 i⟩

/--
Returns the next position in a string after position `p`. If `p` is not a valid position or `p = s.endPos`,
the result is unspecified.

Examples:
Given `def abc := "abc"` and `def lean := "L∃∀N"`,
* `abc.get (0 |> abc.next) = 'b'`
* `lean.get (0 |> lean.next |> lean.next) = '∀'`

Cases where the result is unspecified:
* `"abc".next ⟨3⟩`, since `3 = s.endPos`
* `"L∃∀N".next ⟨2⟩`, since `2` points into the middle of a multi-byte UTF-8 character
-/
@[extern "lean_string_utf8_next"]
def next (s : @& String) (p : @& Pos) : Pos :=
  let c := get s p
  p + c

def utf8PrevAux : List Char → Pos → Pos → Pos
  | [],    _, _ => 0
  | c::cs, i, p =>
    let i' := i + c
    if i' = p then i else utf8PrevAux cs i' p

/--
Returns the position in a string before a specified position, `p`. If `p = ⟨0⟩`, returns `0`.
If `p` is not a valid position, the result is unspecified.

Examples:
Given `def abc := "abc"` and `def lean := "L∃∀N"`,
* `abc.get (abc.endPos |> abc.prev) = 'c'`
* `lean.get (lean.endPos |> lean.prev |> lean.prev |> lean.prev) = '∃'`
* `"L∃∀N".prev ⟨3⟩` is unspecified, since byte 3 occurs in the middle of the multi-byte character `'∃'`.
-/
@[extern "lean_string_utf8_prev"]
def prev : (@& String) → (@& Pos) → Pos
  | ⟨s⟩, p => if p = 0 then 0 else utf8PrevAux s 0 p

/--
Returns `true` if a specified position is greater than or equal to the position which
points to the end of a string. Otherwise, returns `false`.

Examples:
Given `def abc := "abc"` and `def lean := "L∃∀N"`,
* `(0 |> abc.next |> abc.next |> abc.atEnd) = false`
* `(0 |> abc.next |> abc.next |> abc.next |> abc.next |> abc.atEnd) = true`
* `(0 |> lean.next |> lean.next |> lean.next |> lean.next |> lean.atEnd) = true`

Because `"L∃∀N"` contains multi-byte characters, `lean.next (lean.next 0)` is not equal to `abc.next (abc.next 0)`.
-/
@[extern "lean_string_utf8_at_end"]
def atEnd : (@& String) → (@& Pos) → Bool
  | s, p => p.byteIdx ≥ utf8ByteSize s

/--
Returns the character at position `p` of a string.
If `p` is not a valid position, returns `(default : Char)`.

Requires evidence, `h`, that `p` is within bounds
instead of performing a runtime bounds check as in `get`.

Examples:
* `"abc".get' 0 (by decide) = 'a'`
* `let lean := "L∃∀N"; lean.get' (0 |> lean.next |> lean.next) (by decide) = '∀'`

A typical pattern combines `get'` with a dependent if-else expression
to avoid the overhead of an additional bounds check. For example:
```
def getInBounds? (s : String) (p : String.Pos) : Option Char :=
  if h : s.atEnd p then none else some (s.get' p h)
```

Even with evidence of `¬ s.atEnd p`,
`p` may be invalid if a byte index points into the middle of a multi-byte UTF-8 character.
For example, `"L∃∀N".get' ⟨2⟩ (by decide) = (default : Char)`.
-/
@[extern "lean_string_utf8_get_fast"]
def get' (s : @& String) (p : @& Pos) (h : ¬ s.atEnd p) : Char :=
  match s with
  | ⟨s⟩ => utf8GetAux s 0 p

/--
Returns the next position in a string after position `p`.
If `p` is not a valid position, the result is unspecified.

Requires evidence, `h`, that `p` is within bounds
instead of performing a runtime bounds check as in `next`.

Examples:
* `let abc := "abc"; abc.get (abc.next' 0 (by decide)) = 'b'`

A typical pattern combines `next'` with a dependent if-else expression
to avoid the overhead of an additional bounds check. For example:
```
def next? (s: String) (p : String.Pos) : Option Char :=
  if h : s.atEnd p then none else s.get (s.next' p h)
```
-/
@[extern "lean_string_utf8_next_fast"]
def next' (s : @& String) (p : @& Pos) (h : ¬ s.atEnd p) : Pos :=
  let c := get s p
  p + c

@[extern "lean_string_utf8_extract"]
def extract : (@& String) → (@& Pos) → (@& Pos) → String
  | ⟨s⟩, b, e => if b.byteIdx ≥ e.byteIdx then "" else ⟨go₁ s 0 b e⟩
where
  go₁ : List Char → Pos → Pos → Pos → List Char
    | [],        _, _, _ => []
    | s@(c::cs), i, b, e => if i = b then go₂ s i e else go₁ cs (i + c) b e

  go₂ : List Char → Pos → Pos → List Char
    | [],    _, _ => []
    | c::cs, i, e => if i = e then [] else c :: go₂ cs (i + c) e


end String
