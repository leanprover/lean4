/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Gabriel Ebner, Marc Huisinga
-/
import Lean.Data.Json.Basic
import Lean.Data.Json.Printer

namespace Lean

universe u

class FromJson (α : Type u) where
  fromJson? : Json → Except String α

export FromJson (fromJson?)

class ToJson (α : Type u) where
  toJson : α → Json

export ToJson (toJson)

instance : FromJson Json := ⟨Except.ok⟩
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

instance [FromJson α] : FromJson (Array α) where
  fromJson?
    | Json.arr a => a.mapM fromJson?
    | _          => throw "JSON array expected"

instance [ToJson α] : ToJson (Array α) :=
  ⟨fun a => Json.arr (a.map toJson)⟩

instance [FromJson α] : FromJson (Option α) where
  fromJson?
    | Json.null => Except.ok none
    | j         => some <$> fromJson? j

instance [ToJson α] : ToJson (Option α) :=
  ⟨fun
    | none   => Json.null
    | some a => toJson a⟩

instance : FromJson Name where
  fromJson? j := do
    let s ← j.getStr?
    let some n ← Syntax.decodeNameLit s
      | throw s!"expected a `Name`, got '{j}'"
    return n

instance : ToJson Name where
  toJson n := toString (repr n)

/- Note that `USize`s are stored as strings because JavaScript
cannot represent 64-bit numbers. -/
instance : FromJson USize where
  fromJson? j := do
    let s ← j.getStr?
    let some v ← Syntax.decodeNatLitVal? s -- TODO maybe this should be in Std
      | throw s!"expected a string-encoded `USize`, got '{j}'"
    if v ≥ USize.size then
      throw "value '{j}' is too large for `USize`"
    return USize.ofNat v

instance : ToJson USize where
  toJson v := toString (repr v)

namespace Json

instance : FromJson Structured := ⟨fun
  | arr a => Structured.arr a
  | obj o => Structured.obj o
  | _     => throw "structured object expected"⟩

instance : ToJson Structured := ⟨fun
  | Structured.arr a => arr a
  | Structured.obj o => obj o⟩

def toStructured? [ToJson α] (v : α) : Except String Structured :=
  fromJson? (toJson v)

def getObjValAs? (j : Json) (α : Type u) [FromJson α] (k : String) : Except String α :=
  fromJson? <| j.getObjValD k

def opt [ToJson α] (k : String) : Option α → List (String × Json)
  | none   => []
  | some o => [⟨k, toJson o⟩]

/-- Parses a JSON-encoded `structure` or `inductive` constructor. Used mostly by `deriving FromJson`. -/
def parseTagged
    (json : Json)
    (tag : String)
    (nFields : Nat)
    (fieldNames? : Option (Array Name)) : Except String (Array Json) :=
  if nFields == 0 then
    match getStr? json with
    | Except.ok s => if s == tag then Except.ok #[] else throw s!"incorrect tag: {s} ≟ {tag}"
    | Except.error err => Except.error err
  else
    match getObjVal? json tag with
    | Except.ok payload =>
      match fieldNames? with
      | some fieldNames =>
        do
          let mut fields := #[]
          for fieldName in fieldNames do
            fields := fields.push (←getObjVal? payload fieldName.getString!)
          Except.ok fields
      | none =>
        if nFields == 1 then
          Except.ok #[payload]
        else
          match getArr? payload with
          | Except.ok fields =>
            if fields.size == nFields then
              Except.ok fields
            else
              Except.error s!"incorrect number of fields: {fields.size} ≟ {nFields}"
          | Except.error err => Except.error err
    | Except.error err => Except.error err

end Json
end Lean
