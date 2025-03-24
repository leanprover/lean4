/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Data.Format.Basic
open Sum Subtype Nat

open Std

/--
A typeclass that specifies the standard way of turning values of some type into `Format`.

When rendered this `Format` should be as close as possible to something that can be parsed as the
input value.
-/
class Repr (α : Type u) where
  /--
  Turn a value of type `α` into `Format` at a given precedence. The precedence value can be used
  to avoid parentheses if they are not necessary.
  -/
  reprPrec : α → Nat → Format

export Repr (reprPrec)

/--
Turn `a` into `Format` using its `Repr` instance. The precedence level is initially set to 0.
-/
abbrev repr [Repr α] (a : α) : Format :=
  reprPrec a 0

abbrev reprStr [Repr α] (a : α) : String :=
  reprPrec a 0 |>.pretty

abbrev reprArg [Repr α] (a : α) : Format :=
  reprPrec a max_prec

/-- Auxiliary class for marking types that should be considered atomic by `Repr` methods.
   We use it at `Repr (List α)` to decide whether `bracketFill` should be used or not. -/
class ReprAtom (α : Type u)

-- This instance is needed because `id` is not reducible
instance [Repr α] : Repr (id α) :=
  inferInstanceAs (Repr α)

instance [Repr α] : Repr (Id α) :=
  inferInstanceAs (Repr α)

/-
This instance allows us to use `Empty` as a type parameter without causing instance synthesis to fail.
-/
instance : Repr Empty where
  reprPrec := nofun

instance : Repr Bool where
  reprPrec
    | true, _  => "true"
    | false, _ => "false"

def Repr.addAppParen (f : Format) (prec : Nat) : Format :=
  if prec >= max_prec then
    Format.paren f
  else
    f

instance : Repr (Decidable p) where
  reprPrec
    | Decidable.isTrue _, prec  => Repr.addAppParen "isTrue _" prec
    | Decidable.isFalse _, prec => Repr.addAppParen "isFalse _" prec

instance : Repr PUnit.{u+1} where
  reprPrec _ _ := "PUnit.unit"

instance [Repr α] : Repr (ULift.{v} α) where
  reprPrec v prec :=
    Repr.addAppParen ("ULift.up " ++ reprArg v.1) prec

instance : Repr Unit where
  reprPrec _ _ := "()"

/--
Returns a representation of an optional value that should be able to be parsed as an equivalent
optional value.

This function is typically accessed through the `Repr (Option α)` instance.
-/
protected def Option.repr [Repr α] : Option α → Nat → Format
  | none,    _   => "none"
  | some a, prec => Repr.addAppParen ("some " ++ reprArg a) prec

instance [Repr α] : Repr (Option α) where
  reprPrec := Option.repr

protected def Sum.repr [Repr α] [Repr β] : Sum α β → Nat → Format
  | Sum.inl a, prec => Repr.addAppParen ("Sum.inl " ++ reprArg a) prec
  | Sum.inr b, prec => Repr.addAppParen ("Sum.inr " ++ reprArg b) prec

instance [Repr α] [Repr β] : Repr (Sum α β) where
  reprPrec := Sum.repr

class ReprTuple (α : Type u) where
  reprTuple : α → List Format → List Format

export ReprTuple (reprTuple)

instance [Repr α] : ReprTuple α where
  reprTuple a xs := repr a :: xs

instance [Repr α] [ReprTuple β] : ReprTuple (α × β) where
  reprTuple | (a, b), xs => reprTuple b (repr a :: xs)

protected def Prod.repr [Repr α] [ReprTuple β] : α × β → Nat → Format
  | (a, b), _ => Format.bracket "(" (Format.joinSep (reprTuple b [repr a]).reverse ("," ++ Format.line)) ")"

instance [Repr α] [ReprTuple β] : Repr (α × β) where
  reprPrec := Prod.repr

instance {β : α → Type v} [Repr α] [(x : α) → Repr (β x)] : Repr (Sigma β) where
  reprPrec | ⟨a, b⟩, _ => Format.bracket "⟨" (repr a ++ ", " ++ repr b) "⟩"

instance {p : α → Prop} [Repr α] : Repr (Subtype p) where
  reprPrec s prec := reprPrec s.val prec

namespace Nat

/-
We have pure functions for calculating the decimal representation of a `Nat` (`toDigits`), but also
a fast variant that handles small numbers (`USize`) via C code (`lean_string_of_usize`).
-/

/--
Returns a single digit representation of `n`, which is assumed to be in a base less than or equal to
`16`. Returns `'*'` if `n > 15`.

Examples:
 * `Nat.digitChar 5 = '5'`
 * `Nat.digitChar 12 = 'c'`
 * `Nat.digitChar 15 = 'f'`
 * `Nat.digitChar 16 = '*'`
 * `Nat.digitChar 85 = '*'`
-/
def digitChar (n : Nat) : Char :=
  if n = 0 then '0' else
  if n = 1 then '1' else
  if n = 2 then '2' else
  if n = 3 then '3' else
  if n = 4 then '4' else
  if n = 5 then '5' else
  if n = 6 then '6' else
  if n = 7 then '7' else
  if n = 8 then '8' else
  if n = 9 then '9' else
  if n = 0xa then 'a' else
  if n = 0xb then 'b' else
  if n = 0xc then 'c' else
  if n = 0xd then 'd' else
  if n = 0xe then 'e' else
  if n = 0xf then 'f' else
  '*'

def toDigitsCore (base : Nat) : Nat → Nat → List Char → List Char
  | 0,      _, ds => ds
  | fuel+1, n, ds =>
    let d  := digitChar <| n % base;
    let n' := n / base;
    if n' = 0 then d::ds
    else toDigitsCore base fuel n' (d::ds)

/--
Returns the decimal representation of a natural number as a list of digit characters in the given
base. If the base is greater than `16` then `'*'` is returned for digits greater than `0xf`.

Examples:
* `Nat.toDigits 10 0xff = ['2', '5', '5']`
* `Nat.toDigits 8 0xc = ['1', '4']`
* `Nat.toDigits 16 0xcafe = ['c', 'a', 'f', 'e']`
* `Nat.toDigits 80 200 = ['2', '*']`
-/
def toDigits (base : Nat) (n : Nat) : List Char :=
  toDigitsCore base (n+1) n []

/--
Converts a word-sized unsigned integer into a decimal string.

This function is overridden at runtime with an efficient implementation.

Examples:
 * `USize.repr 0 = "0"`
 * `USize.repr 28 = "28"`
 * `USize.repr 307 = "307"`
-/
@[extern "lean_string_of_usize"]
protected def _root_.USize.repr (n : @& USize) : String :=
  (toDigits 10 n.toNat).asString

/-- We statically allocate and memoize reprs for small natural numbers. -/
private def reprArray : Array String := Id.run do
  List.range 128 |>.map (·.toUSize.repr) |> Array.mk

private def reprFast (n : Nat) : String :=
  if h : n < 128 then Nat.reprArray.getInternal n h else
  if h : n < USize.size then (USize.ofNatLT n h).repr
  else (toDigits 10 n).asString

/--
Converts a natural number to its decimal string representation.
-/
@[implemented_by reprFast]
protected def repr (n : Nat) : String :=
  (toDigits 10 n).asString

/--
Converts a natural number less than `10` to the corresponding Unicode superscript digit character.
Returns `'*'` for other numbers.

Examples:
* `Nat.superDigitChar 3 = '³'`
* `Nat.superDigitChar 7 = '⁷'`
* `Nat.superDigitChar 10 = '*'`
-/
def superDigitChar (n : Nat) : Char :=
  if n = 0 then '⁰' else
  if n = 1 then '¹' else
  if n = 2 then '²' else
  if n = 3 then '³' else
  if n = 4 then '⁴' else
  if n = 5 then '⁵' else
  if n = 6 then '⁶' else
  if n = 7 then '⁷' else
  if n = 8 then '⁸' else
  if n = 9 then '⁹' else
  '*'

partial def toSuperDigitsAux : Nat → List Char → List Char
  | n, ds =>
    let d  := superDigitChar <| n % 10;
    let n' := n / 10;
    if n' = 0 then d::ds
    else toSuperDigitsAux n' (d::ds)

/--
Converts a natural number to the list of Unicode superscript digit characters that corresponds to
its decimal representation.

Examples:
 * `Nat.toSuperDigits 0 = ['⁰']`
 * `Nat.toSuperDigits 35 = ['³', '⁵']`
-/
def toSuperDigits (n : Nat) : List Char :=
  toSuperDigitsAux n []

/--
Converts a natural number to a string that contains the its decimal representation as Unicode
superscript digit characters.

Examples:
 * `Nat.toSuperscriptString 0 = "⁰"`
 * `Nat.toSuperscriptString 35 = "³⁵"`
-/
def toSuperscriptString (n : Nat) : String :=
  (toSuperDigits n).asString

/--
Converts a natural number less than `10` to the corresponding Unicode subscript digit character.
Returns `'*'` for other numbers.

Examples:
* `Nat.subDigitChar 3 = '₃'`
* `Nat.subDigitChar 7 = '₇'`
* `Nat.subDigitChar 10 = '*'`
-/
def subDigitChar (n : Nat) : Char :=
  if n = 0 then '₀' else
  if n = 1 then '₁' else
  if n = 2 then '₂' else
  if n = 3 then '₃' else
  if n = 4 then '₄' else
  if n = 5 then '₅' else
  if n = 6 then '₆' else
  if n = 7 then '₇' else
  if n = 8 then '₈' else
  if n = 9 then '₉' else
  '*'

partial def toSubDigitsAux : Nat → List Char → List Char
  | n, ds =>
    let d  := subDigitChar <| n % 10;
    let n' := n / 10;
    if n' = 0 then d::ds
    else toSubDigitsAux n' (d::ds)

/--
Converts a natural number to the list of Unicode subscript digit characters that corresponds to
its decimal representation.

Examples:
 * `Nat.toSubDigits 0 = ['₀']`
 * `Nat.toSubDigits 35 = ['₃', '₅']`
-/
def toSubDigits (n : Nat) : List Char :=
  toSubDigitsAux n []

/--
Converts a natural number to a string that contains the its decimal representation as Unicode
subscript digit characters.

Examples:
 * `Nat.toSubscriptString 0 = "₀"`
 * `Nat.toSubscriptString 35 = "₃₅"`
-/
def toSubscriptString (n : Nat) : String :=
  (toSubDigits n).asString

end Nat

instance : Repr Nat where
  reprPrec n _ := Nat.repr n

/--
Returns the decimal string representation of an integer.
-/
protected def Int.repr : Int → String
    | ofNat m   => Nat.repr m
    | negSucc m => "-" ++ Nat.repr (succ m)

instance : Repr Int where
  reprPrec i prec := if i < 0 then Repr.addAppParen i.repr prec else i.repr

def hexDigitRepr (n : Nat) : String :=
  String.singleton <| Nat.digitChar n

def Char.quoteCore (c : Char) : String :=
  if       c = '\n' then "\\n"
  else if  c = '\t' then "\\t"
  else if  c = '\\' then "\\\\"
  else if  c = '\"' then "\\\""
  else if  c.toNat <= 31 ∨ c = '\x7f' then "\\x" ++ smallCharToHex c
  else String.singleton c
where
  smallCharToHex (c : Char) : String :=
    let n  := Char.toNat c;
    let d2 := n / 16;
    let d1 := n % 16;
    hexDigitRepr d2 ++ hexDigitRepr d1

/--
Quotes the character to its representation as a character literal, surrounded by single quotes and
escaped as necessary.

Examples:
 * `'L'.quote = "'L'"`
 * `'"'.quote = "'\\\"'"`
-/
def Char.quote (c : Char) : String :=
  "'" ++ Char.quoteCore c ++ "'"

instance : Repr Char where
  reprPrec c _ := c.quote

protected def Char.repr (c : Char) : String :=
  c.quote

/--
Converts a string to its corresponding Lean string literal syntax. Double quotes are added to each
end, and internal characters are escaped as needed.

Examples:
* `"abc".quote = "\"abc\""`
* `"\"".quote = "\"\\\"\""`
-/
def String.quote (s : String) : String :=
  if s.isEmpty then "\"\""
  else s.foldl (fun s c => s ++ c.quoteCore) "\"" ++ "\""

instance : Repr String where
  reprPrec s _ := s.quote

instance : Repr String.Pos where
  reprPrec p _ := "{ byteIdx := " ++ repr p.byteIdx ++ " }"

instance : Repr Substring where
  reprPrec s _ := Format.text <| String.quote s.toString ++ ".toSubstring"

instance : Repr String.Iterator where
  reprPrec | ⟨s, pos⟩, prec => Repr.addAppParen ("String.Iterator.mk " ++ reprArg s ++ " " ++ reprArg pos) prec

instance (n : Nat) : Repr (Fin n) where
  reprPrec f _ := repr f.val

instance : Repr UInt8 where
  reprPrec n _ := repr n.toNat

instance : Repr UInt16 where
  reprPrec n _ := repr n.toNat

instance : Repr UInt32 where
  reprPrec n _ := repr n.toNat

instance : Repr UInt64 where
  reprPrec n _ := repr n.toNat

instance : Repr USize where
  reprPrec n _ := repr n.toNat

protected def List.repr [Repr α] (a : List α) (n : Nat) : Format :=
  let _ : ToFormat α := ⟨repr⟩
  match a, n with
  | [], _ => "[]"
  | as, _ => Format.bracket "[" (Format.joinSep as ("," ++ Format.line)) "]"

instance [Repr α] : Repr (List α) where
  reprPrec := List.repr

protected def List.repr' [Repr α] [ReprAtom α] (a : List α) (n : Nat) : Format :=
  let _ : ToFormat α := ⟨repr⟩
  match a, n with
  | [], _ => "[]"
  | as, _ => Format.bracketFill "[" (Format.joinSep as ("," ++ Format.line)) "]"

instance [Repr α] [ReprAtom α] : Repr (List α) where
  reprPrec := List.repr'

instance : ReprAtom Bool   := ⟨⟩
instance : ReprAtom Nat    := ⟨⟩
instance : ReprAtom Int    := ⟨⟩
instance : ReprAtom Char   := ⟨⟩
instance : ReprAtom String := ⟨⟩
instance : ReprAtom UInt8  := ⟨⟩
instance : ReprAtom UInt16 := ⟨⟩
instance : ReprAtom UInt32 := ⟨⟩
instance : ReprAtom UInt64 := ⟨⟩
instance : ReprAtom USize  := ⟨⟩

deriving instance Repr for Lean.SourceInfo
