/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.string.basic init.data.uint init.data.nat.div
open sum subtype nat

universes u v

class hasRepr (α : Type u) :=
(repr : α → string)

export hasRepr (repr)

-- This instance is needed because `id` is not reducible
instance {α : Type u} [hasRepr α] : hasRepr (id α) :=
inferInstanceAs (hasRepr α)

instance : hasRepr bool :=
⟨λ b, cond b "tt" "ff"⟩

instance {p : Prop} : hasRepr (decidable p) :=
⟨λ b : decidable p, @ite p b _ "tt" "ff"⟩

protected def list.reprAux {α : Type u} [hasRepr α] : bool → list α → string
| b  []      := ""
| tt (x::xs) := repr x ++ list.reprAux ff xs
| ff (x::xs) := ", " ++ repr x ++ list.reprAux ff xs

protected def list.repr {α : Type u} [hasRepr α] : list α → string
| []      := "[]"
| (x::xs) := "[" ++ list.reprAux tt (x::xs) ++ "]"

instance {α : Type u} [hasRepr α] : hasRepr (list α) :=
⟨list.repr⟩

instance : hasRepr unit :=
⟨λ u, "()"⟩

instance {α : Type u} [hasRepr α] : hasRepr (option α) :=
⟨λ o, match o with | none := "none" | (some a) := "(some " ++ repr a ++ ")"⟩

instance {α : Type u} {β : Type v} [hasRepr α] [hasRepr β] : hasRepr (α ⊕ β) :=
⟨λ s, match s with | (inl a) := "(inl " ++ repr a ++ ")" | (inr b) := "(inr " ++ repr b ++ ")"⟩

instance {α : Type u} {β : Type v} [hasRepr α] [hasRepr β] : hasRepr (α × β) :=
⟨λ ⟨a, b⟩, "(" ++ repr a ++ ", " ++ repr b ++ ")"⟩

instance {α : Type u} {β : α → Type v} [hasRepr α] [s : ∀ x, hasRepr (β x)] : hasRepr (sigma β) :=
⟨λ ⟨a, b⟩, "⟨"  ++ repr a ++ ", " ++ repr b ++ "⟩"⟩

instance {α : Type u} {p : α → Prop} [hasRepr α] : hasRepr (subtype p) :=
⟨λ s, repr (val s)⟩

namespace nat

def digitChar (n : ℕ) : char :=
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

def toDigitsCore (base : nat) : nat → nat → list char → list char
| 0        n ds := ds
| (fuel+1) n ds :=
  let d  := digitChar $ n % base in
  let n' := n / base in
  if n' = 0 then d::ds
  else toDigitsCore fuel n' (d::ds)

def toDigits (base : nat) (n : nat) : list char :=
toDigitsCore base (n+1) n []

protected def repr (n : ℕ) : string :=
(toDigits 10 n).asString

end nat

instance : hasRepr nat :=
⟨nat.repr⟩

def hexDigitRepr (n : nat) : string :=
string.singleton $ nat.digitChar n

def charToHex (c : char) : string :=
let n  := char.toNat c,
    d2 := n / 16,
    d1 := n % 16
in hexDigitRepr d2 ++ hexDigitRepr d1

def char.quoteCore (c : char) : string :=
if       c = '\n' then "\\n"
else if  c = '\t' then "\\t"
else if  c = '\\' then "\\\\"
else if  c = '\"' then "\\\""
else if  c.toNat <= 31 ∨ c = '\x7f' then "\\x" ++ charToHex c
else string.singleton c

instance : hasRepr char :=
⟨λ c, "'" ++ char.quoteCore c ++ "'"⟩

def string.quoteAux : list char → string
| []      := ""
| (x::xs) := char.quoteCore x ++ string.quoteAux xs

def string.quote (s : string) : string :=
if s.isEmpty = tt then "\"\""
else "\"" ++ string.quoteAux s.toList ++ "\""

instance : hasRepr string :=
⟨string.quote⟩

instance : hasRepr string.iterator :=
⟨λ it, it.remainingToString.quote ++ ".mkIterator"⟩

instance (n : nat) : hasRepr (fin n) :=
⟨λ f, repr (fin.val f)⟩

instance : hasRepr uint16 := ⟨λ n, repr n.toNat⟩
instance : hasRepr uint32 := ⟨λ n, repr n.toNat⟩
instance : hasRepr uint64 := ⟨λ n, repr n.toNat⟩
instance : hasRepr usize  := ⟨λ n, repr n.toNat⟩

def char.repr (c : char) : string :=
repr c
