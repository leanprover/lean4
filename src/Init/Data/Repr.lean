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

def toDigits (base : Nat) (n : Nat) : List Char :=
  toDigitsCore base (n+1) n []

@[extern "lean_string_of_usize"]
protected def _root_.USize.repr (n : @& USize) : String :=
  (toDigits 10 n.toNat).asString

/-- We statically allocate and memoize reprs for small natural numbers. -/
private def reprArray : Array String := Id.run do
  List.range 128 |>.map (·.toUSize.repr) |> Array.mk

private def reprFast (n : Nat) : String :=
  if h : n < 128 then Nat.reprArray.get n h else
  if h : n < USize.size then (USize.ofNatCore n h).repr
  else (toDigits 10 n).asString

@[implemented_by reprFast]
protected def repr (n : Nat) : String :=
  (toDigits 10 n).asString

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

def toSuperDigits (n : Nat) : List Char :=
  toSuperDigitsAux n []

def toSuperscriptString (n : Nat) : String :=
  (toSuperDigits n).asString

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

def toSubDigits (n : Nat) : List Char :=
  toSubDigitsAux n []

def toSubscriptString (n : Nat) : String :=
  (toSubDigits n).asString

end Nat

instance : Repr Nat where
  reprPrec n _ := Nat.repr n

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

def Char.quote (c : Char) : String :=
  "'" ++ Char.quoteCore c ++ "'"

instance : Repr Char where
  reprPrec c _ := c.quote

protected def Char.repr (c : Char) : String :=
  c.quote

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
