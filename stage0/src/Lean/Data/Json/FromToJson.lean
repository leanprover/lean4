/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Gabriel Ebner, Marc Huisinga
-/
import Lean.Data.Json.Basic

namespace Lean

universes u

class FromJson (α : Type u) where
  fromJson? : Json → Option α

export FromJson (fromJson?)

class ToJson (α : Type u) where
  toJson : α → Json

export ToJson (toJson)

instance : FromJson Json := ⟨some⟩
instance : ToJson Json := ⟨id⟩

instance : FromJson JsonNumber := ⟨Json.getNum?⟩
instance : ToJson JsonNumber := ⟨Json.num⟩

-- looks like id, but there are coercions happening
instance : FromJson Bool := ⟨Json.getBool?⟩
instance : ToJson Bool := ⟨fun b => b⟩
instance : FromJson Nat := ⟨Json.getNat?⟩
instance : ToJson Nat := ⟨fun n => n⟩
instance : FromJson Int := ⟨Json.getInt?⟩
instance : ToJson Int := ⟨fun n => Json.num n⟩
instance : FromJson String := ⟨Json.getStr?⟩
instance : ToJson String := ⟨fun s => s⟩

instance {α : Type u} [FromJson α] : FromJson (Array α) := ⟨fun j =>
  match j with
  | Json.arr a => a.mapM fromJson?
  | _ => none⟩

instance {α : Type u} [ToJson α] : ToJson (Array α) :=
  ⟨fun a => Json.arr (a.map toJson)⟩

namespace Json

instance : FromJson Structured := ⟨fun j =>
  match j with
  | arr a => Structured.arr a
  | obj o => Structured.obj o
  | _     => none⟩

instance : ToJson Structured := ⟨fun s =>
  match s with
  | Structured.arr a => arr a
  | Structured.obj o => obj o⟩

def getObjValAs? (j : Json) (α : Type u) [FromJson α] (k : String) : Option α :=
  (j.getObjVal? k).bind fromJson?

def opt {α : Type u} [ToJson α] (k : String) : Option α → List (String × Json)
  | some o => [⟨k, toJson o⟩]
  | none   => []

end Json
end Lean
