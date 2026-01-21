/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Gabriel Ebner, Marc Huisinga
-/
module

prelude
public import Lean.Data.Json.Printer

public section

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

instance : FromJson Empty where
  fromJson? j := throw (s!"type Empty has no constructor to match JSON value '{j}'. \
                           This occurs when deserializing a value for type Empty, \
                           e.g. at type Option Empty with code for the 'some' constructor.")

instance : ToJson Empty := ⟨nofun⟩
-- looks like id, but there are coercions happening
instance : FromJson Bool := ⟨Json.getBool?⟩
instance : ToJson Bool := ⟨fun b => b⟩
instance : FromJson Nat := ⟨Json.getNat?⟩
instance : ToJson Nat := ⟨fun n => n⟩
instance : FromJson Int := ⟨Json.getInt?⟩
instance : ToJson Int := ⟨fun n => Json.num n⟩
instance : FromJson String := ⟨Json.getStr?⟩
instance : ToJson String := ⟨fun s => s⟩
instance : FromJson String.Slice := ⟨Except.map String.toSlice ∘ Json.getStr?⟩
instance : ToJson String.Slice := ⟨fun s => s.copy⟩

instance : FromJson System.FilePath := ⟨fun j => System.FilePath.mk <$> Json.getStr? j⟩
instance : ToJson System.FilePath := ⟨fun p => p.toString⟩

protected def _root_.Array.fromJson? [FromJson α] : Json → Except String (Array α)
  | Json.arr a => a.mapM fromJson?
  | j          => throw s!"expected JSON array, got '{j}'"

instance [FromJson α] : FromJson (Array α) where
  fromJson? := Array.fromJson?

protected def _root_.Array.toJson [ToJson α] (a : Array α) : Json :=
  Json.arr (a.map toJson)

instance [ToJson α] : ToJson (Array α) where
  toJson := Array.toJson

protected def _root_.List.fromJson? [FromJson α] (j : Json) : Except String (List α) :=
  (fromJson? j (α := Array α)).map Array.toList

instance [FromJson α] : FromJson (List α) where
  fromJson? := List.fromJson?

protected def _root_.List.toJson [ToJson α] (a : List α) : Json :=
  toJson a.toArray

instance [ToJson α] : ToJson (List α) where
  toJson := List.toJson

protected def _root_.Option.fromJson? [FromJson α] : Json → Except String (Option α)
  | Json.null => Except.ok none
  | j         => some <$> fromJson? j

instance [FromJson α] : FromJson (Option α) where
  fromJson? := Option.fromJson?

protected def _root_.Option.toJson [ToJson α] : Option α → Json
  | none   => Json.null
  | some a => toJson a

instance [ToJson α] : ToJson (Option α) where
  toJson := Option.toJson

protected def _root_.Prod.fromJson? {α : Type u} {β : Type v} [FromJson α] [FromJson β] : Json → Except String (α × β)
  | Json.arr #[ja, jb] => do
    let ⟨a⟩ : ULift.{v} α := ← (fromJson? ja).map ULift.up
    let ⟨b⟩ : ULift.{u} β := ← (fromJson? jb).map ULift.up
    return (a, b)
  | j => throw s!"expected pair, got '{j}'"

instance {α : Type u} {β : Type v} [FromJson α] [FromJson β] : FromJson (α × β) where
  fromJson? := Prod.fromJson?

protected def _root_.Prod.toJson [ToJson α] [ToJson β] : α × β → Json
  | (a, b) => Json.arr #[toJson a, toJson b]

instance [ToJson α] [ToJson β] : ToJson (α × β) where
  toJson := Prod.toJson

protected def Name.fromJson? (j : Json) : Except String Name := do
  let s ← j.getStr?
  if s == "[anonymous]" then
    return Name.anonymous
  else
    let n := s.toName
    if n.isAnonymous then throw s!"expected a `Name`, got '{j}'"
    return n

instance : FromJson Name where
  fromJson? := Name.fromJson?

instance : ToJson Name where
  toJson n := toString n

protected def NameMap.fromJson? [FromJson α] : Json → Except String (NameMap α)
  | .obj obj => obj.foldlM (init := {}) fun m k v => do
    if k == "[anonymous]" then
      return m.insert .anonymous (← fromJson? v)
    else
      let n := k.toName
      if n.isAnonymous then
        throw s!"expected a `Name`, got '{k}'"
      else
        return m.insert n (← fromJson? v)
  | j => throw s!"expected a `NameMap`, got '{j}'"

instance [FromJson α] : FromJson (NameMap α) where
  fromJson? := NameMap.fromJson?

protected def NameMap.toJson [ToJson α] (m : NameMap α) : Json :=
  Json.obj <| m.foldl (fun n k v => n.insert k.toString (toJson v)) ∅

instance [ToJson α] : ToJson (NameMap α) where
  toJson := NameMap.toJson

/-- Note that `USize`s and `UInt64`s are stored as strings because JavaScript
cannot represent 64-bit numbers. -/
def bignumFromJson? (j : Json) : Except String Nat := do
  let s ← j.getStr?
  let some v := Syntax.decodeNatLitVal? s -- TODO maybe this should be in Std
    | throw s!"expected a string-encoded number, got '{j}'"
  return v

def bignumToJson (n : Nat) : Json :=
  toString n

protected def _root_.USize.fromJson? (j : Json) : Except String USize := do
  let n ← bignumFromJson? j
  if n ≥ USize.size then
    throw s!"value '{j}' is too large for `USize`"
  return USize.ofNat n

instance : FromJson USize where
  fromJson? := USize.fromJson?

instance : ToJson USize where
  toJson v := bignumToJson (USize.toNat v)

protected def _root_.UInt64.fromJson? (j : Json) : Except String UInt64 := do
  let n ← bignumFromJson? j
  if n ≥ UInt64.size then
    throw s!"value '{j}' is too large for `UInt64`"
  return UInt64.ofNat n

instance : FromJson UInt64 where
  fromJson? := UInt64.fromJson?

instance : ToJson UInt64 where
  toJson v := bignumToJson (UInt64.toNat v)

protected def _root_.Float.toJson (x : Float) : Json :=
  match JsonNumber.fromFloat? x with
  | Sum.inl e => Json.str e
  | Sum.inr n => Json.num n

instance : ToJson Float where
  toJson := Float.toJson

protected def _root_.Float.fromJson? : Json → Except String Float
  | (Json.str "Infinity") => Except.ok (1.0 / 0.0)
  | (Json.str "-Infinity") => Except.ok (-1.0 / 0.0)
  | (Json.str "NaN") => Except.ok (0.0 / 0.0)
  | (Json.num jn) => Except.ok jn.toFloat
  | _ => Except.error "Expected a number or a string 'Infinity', '-Infinity', 'NaN'."

instance : FromJson Float where
  fromJson? := Float.fromJson?

namespace Json

protected def Structured.fromJson? : Json → Except String Structured
  | .arr a => return Structured.arr a
  | .obj o => return Structured.obj o
  | j     => throw s!"expected structured object, got '{j}'"

instance : FromJson Structured where
  fromJson? := Structured.fromJson?

protected def Structured.toJson : Structured → Json
  | .arr a => .arr a
  | .obj o => .obj o

instance : ToJson Structured where
  toJson := Structured.toJson

def toStructured? [ToJson α] (v : α) : Except String Structured :=
  fromJson? (toJson v)

def getObjValAs? (j : Json) (α : Type u) [FromJson α] (k : String) : Except String α :=
  fromJson? <| j.getObjValD k

def setObjValAs! (j : Json) {α : Type u} [ToJson α] (k : String) (v : α) : Json :=
  j.setObjVal! k <| toJson v

def opt [ToJson α] (k : String) : Option α → List (String × Json)
  | none   => []
  | some o => [⟨k, toJson o⟩]

/-- Returns the string value or single key name, if any. -/
def getTag? : Json → Option String
  | .str tag => some tag
  | .obj kvs => guard (kvs.size == 1) *> kvs.minKey?
  | _        => none

-- TODO: delete after rebootstrap
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

/--
Parses a JSON-encoded `structure` or `inductive` constructor, assuming the tag has already been
checked and `nFields` is nonzero. Used mostly by `deriving FromJson`.
-/
def parseCtorFields
    (json : Json)
    (tag : String)
    (nFields : Nat)
    (fieldNames? : Option (Array Name)) : Except String (Array Json) := do
  let payload  ← getObjVal? json tag
  match fieldNames? with
  | some fieldNames =>
    fieldNames.mapM (getObjVal? payload ·.getString!)
  | none =>
    if nFields == 1 then
      Except.ok #[payload]
    else
      let fields ← getArr? payload
      if fields.size == nFields then
        Except.ok fields
      else
        Except.error s!"incorrect number of fields: {fields.size} ≟ {nFields}"

end Json
end Lean
