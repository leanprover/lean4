/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Data.String.Basic
import Init.Data.UInt
import Init.Data.Nat.Div
import Init.Data.Repr
import Init.Control.Id
open Sum Subtype Nat

universes u v

class ToString (α : Type u) :=
  (toString : α → String)

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

protected def List.toStringAux {α : Type u} [ToString α] : Bool → List α → String
  | b,     []    => ""
  | true,  x::xs => toString x ++ List.toStringAux false xs
  | false, x::xs => ", " ++ toString x ++ List.toStringAux false xs

protected def List.toString {α : Type u} [ToString α] : List α → String
  | []    => "[]"
  | x::xs => "[" ++ List.toStringAux true (x::xs) ++ "]"

instance {α : Type u} [ToString α] : ToString (List α) :=
  ⟨List.toString⟩

instance : ToString PUnit.{u+1} :=
  ⟨fun _ => "()"⟩

instance {α : Type u} [ToString α] : ToString (ULift.{v} α) :=
  ⟨fun v => toString v.1⟩

instance : ToString Unit :=
  ⟨fun u => "()"⟩

instance : ToString Nat :=
  ⟨fun n => repr n⟩

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

instance {α : Type u} {β : α → Type v} [ToString α] [s : ∀ x, ToString (β x)] : ToString (Sigma β) := ⟨fun ⟨a, b⟩ =>
  "⟨"  ++ toString a ++ ", " ++ toString b ++ "⟩"⟩

instance {α : Type u} {p : α → Prop} [ToString α] : ToString (Subtype p) := ⟨fun s =>
  toString (val s)⟩
