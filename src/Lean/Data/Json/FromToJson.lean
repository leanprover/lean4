/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Gabriel Ebner, Marc Huisinga
-/
prelude
import Lean.Data.Json.Basic
import Init.Data.List.Control

namespace Lean

universes u

class HasFromJson (α : Type u) :=
(fromJson? : Json → Option α)
export HasFromJson (fromJson?)

class HasToJson (α : Type u) :=
(toJson : α → Json)
export HasToJson (toJson)

instance Json.hasFromJson : HasFromJson Json := ⟨some⟩
instance Json.HasToJson : HasToJson Json := ⟨id⟩

instance JsonNumber.hasFromJson : HasFromJson JsonNumber := ⟨Json.getNum?⟩
instance JsonNumber.hasToJson : HasToJson JsonNumber := ⟨Json.num⟩

-- looks like id, but there are coercions happening
instance Bool.hasFromJson : HasFromJson Bool := ⟨Json.getBool?⟩
instance Bool.hasToJson : HasToJson Bool := ⟨fun b => b⟩
instance Nat.hasFromJson : HasFromJson Nat := ⟨Json.getNat?⟩
instance Nat.hasToJson : HasToJson Nat := ⟨fun n => n⟩
instance Int.hasFromJson : HasFromJson Int := ⟨Json.getInt?⟩
instance Int.hasToJson : HasToJson Int := ⟨fun n => Json.num n⟩
instance String.hasFromJson : HasFromJson String := ⟨Json.getStr?⟩
instance String.hasToJson : HasToJson String := ⟨fun s => s⟩

instance Array.hasFromJson {α : Type u} [HasFromJson α] : HasFromJson (Array α) :=
⟨fun j => match j with
  | Json.arr a => a.mapM fromJson?
  | _ => none⟩
instance List.hasToJson {α : Type u} [HasToJson α] : HasToJson (Array α) :=
⟨fun a => Json.arr (a.map toJson)⟩

def Json.getObjValAs? (j : Json) (α : Type u) [HasFromJson α] (k : String) : Option α :=
(j.getObjVal? k).bind fromJson?

end Lean
