/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Data.Repr
import Init.Data.Option.Basic

open Sum Subtype Nat

open Std

/--
Types that can be converted into a string for display.

There is no expectation that the resulting string can be parsed back to the original data (see
`Repr` for a similar class with this expectation).
-/
class ToString (α : Type u) where
  /-- Converts a value into a string. -/
  toString : α → String

export ToString (toString)

-- This instance is needed because `id` is not reducible
instance {α} [ToString α] : ToString (id α) :=
  inferInstanceAs (ToString α)

instance {α} [ToString α] : ToString (Id α) :=
  inferInstanceAs (ToString α)

instance : ToString String :=
  ⟨fun s => s⟩

instance : ToString Substring :=
  ⟨fun s => s.toString⟩

instance : ToString String.Iterator :=
  ⟨fun it => it.remainingToString⟩

instance : ToString Bool :=
  ⟨fun b => cond b "true" "false"⟩

instance {p : Prop} : ToString (Decidable p) := ⟨fun h =>
  match h with
  | Decidable.isTrue _  => "true"
  | Decidable.isFalse _ => "false"⟩

/--
Converts a list into a string, using `ToString.toString` to convert its elements.

The resulting string resembles list literal syntax, with the elements separated by `", "` and
enclosed in square brackets.

The resulting string may not be valid Lean syntax, because there's no such expectation for
`ToString` instances.

Examples:
* `[1, 2, 3].toString = "[1, 2, 3]"`
* `["cat", "dog"].toString = "[cat, dog]"`
* `["cat", "dog", ""].toString = "[cat, dog, ]"`
-/
protected def List.toString [ToString α] : List α → String
  | [] => "[]"
  | [x] => "[" ++ toString x ++ "]"
  | x::xs => xs.foldl (· ++ ", " ++ toString ·) ("[" ++ toString x) |>.push ']'

instance {α : Type u} [ToString α] : ToString (List α) :=
  ⟨List.toString⟩

instance : ToString PUnit.{u+1} :=
  ⟨fun _ => "()"⟩

instance {α : Type u} [ToString α] : ToString (ULift.{v} α) :=
  ⟨fun v => toString v.1⟩

instance : ToString Unit :=
  ⟨fun _ => "()"⟩

instance : ToString Nat :=
  ⟨fun n => Nat.repr n⟩

instance : ToString String.Pos :=
  ⟨fun p => Nat.repr p.byteIdx⟩

instance : ToString Int where
  toString
    | Int.ofNat m   => toString m
    | Int.negSucc m => "-" ++ toString (succ m)

instance : ToString Char :=
  ⟨fun c => c.toString⟩

instance (n : Nat) : ToString (Fin n) :=
  ⟨fun f => toString (Fin.val f)⟩

instance : ToString UInt8 :=
  ⟨fun n => toString n.toNat⟩

instance : ToString UInt16 :=
  ⟨fun n => toString n.toNat⟩

instance : ToString UInt32 :=
  ⟨fun n => toString n.toNat⟩

instance : ToString UInt64 :=
  ⟨fun n => toString n.toNat⟩

instance : ToString USize :=
  ⟨fun n => toString n.toNat⟩

instance : ToString Format where
  toString f := f.pretty

def addParenHeuristic (s : String) : String :=
  if "(".isPrefixOf s || "[".isPrefixOf s || "{".isPrefixOf s || "#[".isPrefixOf s then s
  else if !s.any Char.isWhitespace then s
  else "(" ++ s ++ ")"

instance {α : Type u} [ToString α] : ToString (Option α) := ⟨fun
  | none => "none"
  | (some a) => "(some " ++ addParenHeuristic (toString a) ++ ")"⟩

instance {α : Type u} {β : Type v} [ToString α] [ToString β] : ToString (Sum α β) := ⟨fun
  | (inl a) => "(inl " ++ addParenHeuristic (toString a) ++ ")"
  | (inr b) => "(inr " ++ addParenHeuristic (toString b) ++ ")"⟩

instance {α : Type u} {β : Type v} [ToString α] [ToString β] : ToString (α × β) := ⟨fun (a, b) =>
  "(" ++ toString a ++ ", " ++ toString b ++ ")"⟩

instance {α : Type u} {β : α → Type v} [ToString α] [∀ x, ToString (β x)] : ToString (Sigma β) := ⟨fun ⟨a, b⟩ =>
  "⟨"  ++ toString a ++ ", " ++ toString b ++ "⟩"⟩

instance {α : Type u} {p : α → Prop} [ToString α] : ToString (Subtype p) := ⟨fun s =>
  toString (val s)⟩

/--
Interprets a string as the decimal representation of an integer, returning it. Returns `none` if the
string does not contain a decimal integer.

A string can be interpreted as a decimal integer if it is not empty, its first character is either
`'-'` or a digit, and all remaining characters are digits.

Use `String.isInt` to check whether `String.toInt?` would return `some`. `String.toInt!` is an
alternative that panics instead of returning `none` when the string is not an integer.

Examples:
 * `"".toInt? = none`
 * `"0".toInt? = some 0`
 * `"5".toInt? = some 5`
 * `"-5".toInt? = some (-5)`
 * `"587".toInt? = some 587`
 * `"-587".toInt? = some (-587)`
 * `" 5".toInt? = none`
 * `"2-3".toInt? = none`
 * `"0xff".toInt? = none`
-/
def String.toInt? (s : String) : Option Int := do
  if s.get 0 = '-' then do
    let v ← (s.toSubstring.drop 1).toNat?;
    pure <| - Int.ofNat v
  else
   Int.ofNat <$> s.toNat?

/--
Checks whether the string can be interpreted as the decimal representation of an integer.

A string can be interpreted as a decimal integer if it is not empty, its first character is
`'-'` or a digit, and all subsequent characters are digits. Leading `+` characters are not allowed.

Use `String.toInt?` or `String.toInt!` to convert such a string to an integer.

Examples:
 * `"".isInt = false`
 * `"0".isInt = true`
 * `"-0".isInt = true`
 * `"5".isInt = true`
 * `"587".isInt = true`
 * `"-587".isInt = true`
 * `"+587".isInt = false`
 * `" 5".isInt = false`
 * `"2-3".isInt = false`
 * `"0xff".isInt = false`
-/
def String.isInt (s : String) : Bool :=
  if s.get 0 = '-' then
    (s.toSubstring.drop 1).isNat
  else
    s.isNat

/--
Interprets a string as the decimal representation of an integer, returning it. Panics if the string
does not contain a decimal integer.

A string can be interpreted as a decimal integer if it is not empty, its first character is `'-'` or
a digit, and all remaining characters are digits.

Use `String.isInt` to check whether `String.toInt!` would return a value. `String.toInt?` is a safer
alternative that returns `none` instead of panicking when the string is not an integer.

Examples:
 * `"0".toInt! = 0`
 * `"5".toInt! = 5`
 * `"587".toInt! = 587`
 * `"-587".toInt! = -587`
-/
def String.toInt! (s : String) : Int :=
  match s.toInt? with
  | some v => v
  | none   => panic "Int expected"

instance [ToString ε] [ToString α] : ToString (Except ε α) where
  toString
    | Except.error e => "error: " ++ toString e
    | Except.ok a    => "ok: " ++ toString a

instance [Repr ε] [Repr α] : Repr (Except ε α) where
  reprPrec
    | Except.error e, prec => Repr.addAppParen ("Except.error " ++ reprArg e) prec
    | Except.ok a, prec    => Repr.addAppParen ("Except.ok " ++ reprArg a) prec
