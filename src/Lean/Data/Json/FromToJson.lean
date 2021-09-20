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
    | j          => throw s!"expected JSON array, got '{j}'"

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

instance [FromJson α] [FromJson β] : FromJson (α × β) where
  fromJson?
    | Json.arr #[ja, jb] => do
      let a ← fromJson? ja
      let b ← fromJson? jb
      return (a, b)
    | j => throw s!"expected pair, got '{j}'"

instance [ToJson α] [ToJson β] : ToJson (α × β) where
  toJson := fun (a, b) => Json.arr #[toJson a, toJson b]

instance : FromJson Name where
  fromJson? j := do
    let s ← j.getStr?
    if s == "[anonymous]" then
      return Name.anonymous
    else
      let some n ← Syntax.decodeNameLit ("`" ++ s)
        | throw s!"expected a `Name`, got '{j}'"
      return n

instance : ToJson Name where
  toJson n := toString n

/- Note that `USize`s and `UInt64`s are stored as strings because JavaScript
cannot represent 64-bit numbers. -/
def bignumFromJson? (j : Json) : Except String Nat := do
  let s ← j.getStr?
  let some v ← Syntax.decodeNatLitVal? s -- TODO maybe this should be in Std
    | throw s!"expected a string-encoded number, got '{j}'"
  return v

def bignumToJson (n : Nat) : Json :=
  toString n

instance : FromJson USize where
  fromJson? j := do
    let n ← bignumFromJson? j
    if n ≥ USize.size then
      throw "value '{j}' is too large for `USize`"
    return USize.ofNat n

instance : ToJson USize where
  toJson v := bignumToJson (USize.toNat v)

instance : FromJson UInt64 where
  fromJson? j := do
    let n ← bignumFromJson? j
    if n ≥ UInt64.size then
      throw "value '{j}' is too large for `UInt64`"
    return UInt64.ofNat n

instance : ToJson UInt64 where
  toJson v := bignumToJson (UInt64.toNat v)

namespace Json

instance : FromJson Structured := ⟨fun
  | arr a => Structured.arr a
  | obj o => Structured.obj o
  | j     => throw s!"expected structured object, got '{j}'"⟩

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
