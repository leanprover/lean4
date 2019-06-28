/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.string.basic init.data.uint init.data.nat.div
open Sum Subtype Nat

universes u v

class HasRepr (α : Type u) :=
(repr : α → String)

export HasRepr (repr)

-- This instance is needed because `id` is not reducible
instance {α : Type u} [HasRepr α] : HasRepr (id α) :=
inferInstanceAs (HasRepr α)

instance : HasRepr Bool :=
⟨λ b, cond b "true" "false"⟩

instance {p : Prop} : HasRepr (Decidable p) :=
⟨λ b : Decidable p, @ite p b _ "true" "false"⟩

protected def List.reprAux {α : Type u} [HasRepr α] : Bool → List α → String
| b     []      := ""
| true  (x::xs) := repr x ++ List.reprAux false xs
| false (x::xs) := ", " ++ repr x ++ List.reprAux false xs

protected def List.repr {α : Type u} [HasRepr α] : List α → String
| []      := "[]"
| (x::xs) := "[" ++ List.reprAux true (x::xs) ++ "]"

instance {α : Type u} [HasRepr α] : HasRepr (List α) :=
⟨List.repr⟩

instance : HasRepr Unit :=
⟨λ u, "()"⟩

instance {α : Type u} [HasRepr α] : HasRepr (Option α) :=
⟨λ o, match o with | none := "none" | (some a) := "(some " ++ repr a ++ ")"⟩

instance {α : Type u} {β : Type v} [HasRepr α] [HasRepr β] : HasRepr (α ⊕ β) :=
⟨λ s, match s with | (inl a) := "(inl " ++ repr a ++ ")" | (inr b) := "(inr " ++ repr b ++ ")"⟩

instance {α : Type u} {β : Type v} [HasRepr α] [HasRepr β] : HasRepr (α × β) :=
⟨λ ⟨a, b⟩, "(" ++ repr a ++ ", " ++ repr b ++ ")"⟩

instance {α : Type u} {β : α → Type v} [HasRepr α] [s : ∀ x, HasRepr (β x)] : HasRepr (Sigma β) :=
⟨λ ⟨a, b⟩, "⟨"  ++ repr a ++ ", " ++ repr b ++ "⟩"⟩

instance {α : Type u} {p : α → Prop} [HasRepr α] : HasRepr (Subtype p) :=
⟨λ s, repr (val s)⟩

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
| 0        n ds := ds
| (fuel+1) n ds :=
  let d  := digitChar $ n % base;
  let n' := n / base;
  if n' = 0 then d::ds
  else toDigitsCore fuel n' (d::ds)

def toDigits (base : Nat) (n : Nat) : List Char :=
toDigitsCore base (n+1) n []

protected def repr (n : Nat) : String :=
(toDigits 10 n).asString

end Nat

instance : HasRepr Nat :=
⟨Nat.repr⟩

def hexDigitRepr (n : Nat) : String :=
String.singleton $ Nat.digitChar n

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

instance : HasRepr Char :=
⟨λ c, "'" ++ Char.quoteCore c ++ "'"⟩

def String.quoteAux : List Char → String
| []      := ""
| (x::xs) := Char.quoteCore x ++ String.quoteAux xs

def String.quote (s : String) : String :=
if s.isEmpty = true then "\"\""
else "\"" ++ String.quoteAux s.toList ++ "\""

instance : HasRepr String :=
⟨String.quote⟩

instance : HasRepr Substring :=
⟨λ s, String.quote s.toString ++ ".toSubstring"⟩

instance : HasRepr String.Iterator :=
⟨λ it, it.remainingToString.quote ++ ".mkIterator"⟩

instance (n : Nat) : HasRepr (Fin n) :=
⟨λ f, repr (Fin.val f)⟩

instance : HasRepr UInt16 := ⟨λ n, repr n.toNat⟩
instance : HasRepr UInt32 := ⟨λ n, repr n.toNat⟩
instance : HasRepr UInt64 := ⟨λ n, repr n.toNat⟩
instance : HasRepr USize  := ⟨λ n, repr n.toNat⟩

def Char.repr (c : Char) : String :=
repr c
