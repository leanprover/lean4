/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.string.basic init.data.uint init.data.nat.div init.data.repr
open sum subtype nat

universes u v

class hasToString (α : Type u) :=
(toString : α → string)

export hasToString (toString)

-- This instance is needed because `id` is not reducible
instance {α : Type u} [hasToString α] : hasToString (id α) :=
inferInstanceAs (hasToString α)

instance : hasToString string :=
⟨λ s, s⟩

instance : hasToString string.iterator :=
⟨λ it, it.remainingToString⟩

instance : hasToString bool :=
⟨λ b, cond b "tt" "ff"⟩

instance {p : Prop} : hasToString (decidable p) :=
-- Remark: type class inference will not consider local instance `b` in the new elaborator
⟨λ b : decidable p, @ite p b _ "tt" "ff"⟩

protected def list.toStringAux {α : Type u} [hasToString α] : bool → list α → string
| b  []      := ""
| tt (x::xs) := toString x ++ list.toStringAux ff xs
| ff (x::xs) := ", " ++ toString x ++ list.toStringAux ff xs

protected def list.toString {α : Type u} [hasToString α] : list α → string
| []      := "[]"
| (x::xs) := "[" ++ list.toStringAux tt (x::xs) ++ "]"

instance {α : Type u} [hasToString α] : hasToString (list α) :=
⟨list.toString⟩

instance : hasToString unit :=
⟨λ u, "()"⟩

instance : hasToString nat :=
⟨λ n, repr n⟩

instance : hasToString char :=
⟨λ c, c.toString⟩

instance (n : nat) : hasToString (fin n) :=
⟨λ f, toString (fin.val f)⟩

instance : hasToString uint8 :=
⟨λ n, toString n.toNat⟩

instance : hasToString uint16 :=
⟨λ n, toString n.toNat⟩

instance : hasToString uint32 :=
⟨λ n, toString n.toNat⟩

instance : hasToString uint64 :=
⟨λ n, toString n.toNat⟩

instance : hasToString usize :=
⟨λ n, toString n.toNat⟩

instance {α : Type u} [hasToString α] : hasToString (option α) :=
⟨λ o, match o with | none := "none" | (some a) := "(some " ++ toString a ++ ")"⟩

instance {α : Type u} {β : Type v} [hasToString α] [hasToString β] : hasToString (α ⊕ β) :=
⟨λ s, match s with | (inl a) := "(inl " ++ toString a ++ ")" | (inr b) := "(inr " ++ toString b ++ ")"⟩

instance {α : Type u} {β : Type v} [hasToString α] [hasToString β] : hasToString (α × β) :=
⟨λ ⟨a, b⟩, "(" ++ toString a ++ ", " ++ toString b ++ ")"⟩

instance {α : Type u} {β : α → Type v} [hasToString α] [s : ∀ x, hasToString (β x)] : hasToString (sigma β) :=
⟨λ ⟨a, b⟩, "⟨"  ++ toString a ++ ", " ++ toString b ++ "⟩"⟩

instance {α : Type u} {p : α → Prop} [hasToString α] : hasToString (subtype p) :=
⟨λ s, toString (val s)⟩
