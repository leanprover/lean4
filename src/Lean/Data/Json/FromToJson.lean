#lang lean4
/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Gabriel Ebner, Marc Huisinga
-/
import Lean.Data.Json.Basic

namespace Lean

universes u

class HasFromJson (α : Type u) :=
  (fromJson? : Json → Option α)

export HasFromJson (fromJson?)

class HasToJson (α : Type u) :=
  (toJson : α → Json)

export HasToJson (toJson)

instance : HasFromJson Json := ⟨some⟩
instance : HasToJson Json := ⟨id⟩

instance : HasFromJson JsonNumber := ⟨Json.getNum?⟩
instance : HasToJson JsonNumber := ⟨Json.num⟩

-- looks like id, but there are coercions happening
instance : HasFromJson Bool := ⟨Json.getBool?⟩
instance : HasToJson Bool := ⟨fun b => b⟩
instance : HasFromJson Nat := ⟨Json.getNat?⟩
instance : HasToJson Nat := ⟨fun n => n⟩
instance : HasFromJson Int := ⟨Json.getInt?⟩
instance : HasToJson Int := ⟨fun n => Json.num n⟩
instance : HasFromJson String := ⟨Json.getStr?⟩
instance : HasToJson String := ⟨fun s => s⟩

instance {α : Type u} [HasFromJson α] : HasFromJson (Array α) := ⟨fun j =>
  match j with
  | Json.arr a => a.mapM fromJson?
  | _ => none⟩

instance {α : Type u} [HasToJson α] : HasToJson (Array α) :=
  ⟨fun a => Json.arr (a.map toJson)⟩

namespace Json

instance : HasFromJson Structured := ⟨fun j =>
  match j with
  | arr a => Structured.arr a
  | obj o => Structured.obj o
  | _     => none⟩

instance : HasToJson Structured := ⟨fun s =>
  match s with
  | Structured.arr a => arr a
  | Structured.obj o => obj o⟩

def getObjValAs? (j : Json) (α : Type u) [HasFromJson α] (k : String) : Option α :=
  (j.getObjVal? k).bind fromJson?

def opt {α : Type u} [HasToJson α] (k : String) : Option α → List (String × Json)
  | some o => [⟨k, toJson o⟩]
  | none   => []

end Json
end Lean
