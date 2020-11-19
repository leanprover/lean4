/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Data.String.Basic
import Init.Data.UInt
import Init.Data.Nat.Div
import Init.Control.Id
open Sum Subtype Nat

universes u v

class Repr (α : Type u) :=
  (repr : α → String)

export Repr (repr)

-- This instance is needed because `id` is not reducible
instance {α : Type u} [Repr α] : Repr (id α) :=
  inferInstanceAs (Repr α)

instance : Repr Bool :=
  ⟨fun b => cond b "true" "false"⟩

instance {α} [Repr α] : Repr (Id α) :=
  inferInstanceAs (Repr α)

instance {p : Prop} : Repr (Decidable p) := {
  repr := fun h => match h with
  | Decidable.isTrue _  => "true"
  | Decidable.isFalse _ => "false"
}

protected def List.reprAux {α : Type u} [Repr α] : Bool → List α → String
  | b,     []    => ""
  | true,  x::xs => repr x ++ List.reprAux false xs
  | false, x::xs => ", " ++ repr x ++ List.reprAux false xs

protected def List.repr {α : Type u} [Repr α] : List α → String
  | []    => "[]"
  | x::xs => "[" ++ List.reprAux true (x::xs) ++ "]"

instance {α : Type u} [Repr α] : Repr (List α) :=
  ⟨List.repr⟩

instance : Repr PUnit.{u+1} :=
  ⟨fun u => "PUnit.unit"⟩

instance {α : Type u} [Repr α] : Repr (ULift.{v} α) :=
  ⟨fun v => "ULift.up (" ++ repr v.1 ++ ")"⟩

instance : Repr Unit :=
  ⟨fun u => "()"⟩

instance {α : Type u} [Repr α] : Repr (Option α) :=
  ⟨fun | none => "none" | (some a) => "(some " ++ repr a ++ ")"⟩

instance {α : Type u} {β : Type v} [Repr α] [Repr β] : Repr (Sum α β) :=
  ⟨fun | (inl a) => "(inl " ++ repr a ++ ")" | (inr b) => "(inr " ++ repr b ++ ")"⟩

instance {α : Type u} {β : Type v} [Repr α] [Repr β] : Repr (α × β) :=
  ⟨fun ⟨a, b⟩ => "(" ++ repr a ++ ", " ++ repr b ++ ")"⟩

instance {α : Type u} {β : α → Type v} [Repr α] [s : ∀ x, Repr (β x)] : Repr (Sigma β) :=
  ⟨fun ⟨a, b⟩ => "⟨"  ++ repr a ++ ", " ++ repr b ++ "⟩"⟩

instance {α : Type u} {p : α → Prop} [Repr α] : Repr (Subtype p) :=
  ⟨fun s => repr (val s)⟩

namespace Nat

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
  | 0,      n, ds => ds
  | fuel+1, n, ds =>
    let d  := digitChar <| n % base;
    let n' := n / base;
    if n' = 0 then d::ds
    else toDigitsCore base fuel n' (d::ds)

def toDigits (base : Nat) (n : Nat) : List Char :=
  toDigitsCore base (n+1) n []

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

end Nat

instance : Repr Nat :=
  ⟨Nat.repr⟩

def hexDigitRepr (n : Nat) : String :=
  String.singleton <| Nat.digitChar n

def charToHex (c : Char) : String :=
  let n  := Char.toNat c;
  let d2 := n / 16;
  let d1 := n % 16;
  hexDigitRepr d2 ++ hexDigitRepr d1

def Char.quoteCore (c : Char) : String :=
  if       c = '\n' then "\\n"
  else if  c = '\t' then "\\t"
  else if  c = '\\' then "\\\\"
  else if  c = '\"' then "\\\""
  else if  c.toNat <= 31 ∨ c = '\x7f' then "\\x" ++ charToHex c
  else String.singleton c

instance : Repr Char :=
  ⟨fun c => "'" ++ Char.quoteCore c ++ "'"⟩

def String.quote (s : String) : String :=
  if s.isEmpty = true then "\"\""
  else s.foldl (fun s c => s ++ c.quoteCore) "\"" ++ "\""

instance : Repr String :=
  ⟨String.quote⟩

instance : Repr Substring :=
  ⟨fun s => String.quote s.toString ++ ".toSubstring"⟩

instance : Repr String.Iterator :=
  ⟨fun ⟨s, pos⟩ => "(String.Iterator.mk " ++ repr s ++ " " ++ repr pos ++ ")"⟩

instance (n : Nat) : Repr (Fin n) :=
  ⟨fun f => repr (Fin.val f)⟩

instance : Repr UInt16 := ⟨fun n => repr n.toNat⟩
instance : Repr UInt32 := ⟨fun n => repr n.toNat⟩
instance : Repr UInt64 := ⟨fun n => repr n.toNat⟩
instance : Repr USize  := ⟨fun n => repr n.toNat⟩

protected def Char.repr (c : Char) : String :=
  repr c
