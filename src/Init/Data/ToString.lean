/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Data.String.Basic
import Init.Data.UInt
import Init.Data.Nat.Div
import Init.Data.Repr
open Sum Subtype Nat

universes u v

class HasToString (α : Type u) :=
(toString : α → String)

export HasToString (toString)

-- This instance is needed because `id` is not reducible
instance {α : Type u} [HasToString α] : HasToString (id α) :=
inferInstanceAs (HasToString α)

instance : HasToString String :=
⟨fun s => s⟩

instance : HasToString Substring :=
⟨fun s => s.toString⟩

instance : HasToString String.Iterator :=
⟨fun it => it.remainingToString⟩

instance : HasToString Bool :=
⟨fun b => cond b "true" "false"⟩

instance {p : Prop} : HasToString (Decidable p) :=
⟨fun h => match h with
  | Decidable.isTrue _  => "true"
  | Decidable.isFalse _ => "false"⟩

protected def List.toStringAux {α : Type u} [HasToString α] : Bool → List α → String
| b,     []    => ""
| true,  x::xs => toString x ++ List.toStringAux false xs
| false, x::xs => ", " ++ toString x ++ List.toStringAux false xs

protected def List.toString {α : Type u} [HasToString α] : List α → String
| []    => "[]"
| x::xs => "[" ++ List.toStringAux true (x::xs) ++ "]"

instance {α : Type u} [HasToString α] : HasToString (List α) :=
⟨List.toString⟩

instance : HasToString Unit :=
⟨fun u => "()"⟩

instance : HasToString Nat :=
⟨fun n => repr n⟩

instance : HasToString Char :=
⟨fun c => c.toString⟩

instance (n : Nat) : HasToString (Fin n) :=
⟨fun f => toString (Fin.val f)⟩

instance : HasToString UInt8 :=
⟨fun n => toString n.toNat⟩

instance : HasToString UInt16 :=
⟨fun n => toString n.toNat⟩

instance : HasToString UInt32 :=
⟨fun n => toString n.toNat⟩

instance : HasToString UInt64 :=
⟨fun n => toString n.toNat⟩

instance : HasToString USize :=
⟨fun n => toString n.toNat⟩

def addParenHeuristic (s : String) : String :=
if "(".isPrefixOf s || "[".isPrefixOf s || "{".isPrefixOf s || "#[".isPrefixOf s then s
else if !s.any Char.isWhitespace then s
else "(" ++ s ++ ")"

instance {α : Type u} [HasToString α] : HasToString (Option α) :=
⟨fun o => match o with | none => "none" | (some a) => "(some " ++ addParenHeuristic (toString a) ++ ")"⟩

instance {α : Type u} {β : Type v} [HasToString α] [HasToString β] : HasToString (Sum α β) :=
⟨fun s => match s with | (inl a) => "(inl " ++ addParenHeuristic (toString a) ++ ")" | (inr b) => "(inr " ++ addParenHeuristic (toString b) ++ ")"⟩

instance {α : Type u} {β : Type v} [HasToString α] [HasToString β] : HasToString (α × β) :=
⟨fun ⟨a, b⟩ => "(" ++ toString a ++ ", " ++ toString b ++ ")"⟩

instance {α : Type u} {β : α → Type v} [HasToString α] [s : ∀ x, HasToString (β x)] : HasToString (Sigma β) :=
⟨fun ⟨a, b⟩ => "⟨"  ++ toString a ++ ", " ++ toString b ++ "⟩"⟩

instance {α : Type u} {p : α → Prop} [HasToString α] : HasToString (Subtype p) :=
⟨fun s => toString (val s)⟩
