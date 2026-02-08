/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
module

prelude
public import Init.Data.Repr
import Init.Data.Char.Basic

public section

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

instance : ToString Substring.Raw :=
  ⟨fun s => Substring.Raw.Internal.toString s⟩

instance : ToString Char :=
  ⟨fun c => Char.toString c⟩

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
  | [x] => String.Internal.append (String.Internal.append "[" (toString x)) "]"
  | x::xs => String.push (xs.foldl (fun l r => String.Internal.append (String.Internal.append l ", ") (toString r))
      (String.Internal.append "[" (toString x))) ']'

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

instance : ToString String.Pos.Raw :=
  ⟨fun p => Nat.repr p.byteIdx⟩

instance : ToString Int where
  toString
    | Int.ofNat m   => toString m
    | Int.negSucc m => String.Internal.append "-" (toString (succ m))

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
  if String.Internal.isPrefixOf "(" s || String.Internal.isPrefixOf "[" s || String.Internal.isPrefixOf "{" s || String.Internal.isPrefixOf "#[" s then s
  else if !(String.Internal.any s Char.isWhitespace) then s
  else String.Internal.append (String.Internal.append "(" s) ")"

instance {α : Type u} [ToString α] : ToString (Option α) := ⟨fun
  | none => "none"
  | (some a) => String.Internal.append (String.Internal.append "(some " (addParenHeuristic (toString a))) ")"⟩

instance {α : Type u} {β : Type v} [ToString α] [ToString β] : ToString (Sum α β) := ⟨fun
  | (inl a) => String.Internal.append (String.Internal.append "(inl " (addParenHeuristic (toString a))) ")"
  | (inr b) => String.Internal.append (String.Internal.append "(inr " (addParenHeuristic (toString b))) ")"⟩

instance {α : Type u} {β : Type v} [ToString α] [ToString β] : ToString (α × β) := ⟨fun (a, b) =>
  String.Internal.append
    (String.Internal.append
      (String.Internal.append
        (String.Internal.append "(" (toString a))
        ", ")
      (toString b))
    ")"⟩

instance {α : Type u} {β : α → Type v} [ToString α] [∀ x, ToString (β x)] : ToString (Sigma β) := ⟨fun ⟨a, b⟩ =>
  String.Internal.append
    (String.Internal.append
      (String.Internal.append
        (String.Internal.append "⟨" (toString a))
        ", ")
      (toString b))
    "⟩"⟩

instance {α : Type u} {p : α → Prop} [ToString α] : ToString (Subtype p) := ⟨fun s =>
  toString (val s)⟩

instance [ToString ε] [ToString α] : ToString (Except ε α) where
  toString
    | Except.error e => String.Internal.append "error: " (toString e)
    | Except.ok a    => String.Internal.append "ok: " (toString a)

instance [Repr ε] [Repr α] : Repr (Except ε α) where
  reprPrec
    | Except.error e, prec => Repr.addAppParen ("Except.error " ++ reprArg e) prec
    | Except.ok a, prec    => Repr.addAppParen ("Except.ok " ++ reprArg a) prec
