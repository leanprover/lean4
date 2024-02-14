/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Data.Json
import Lean.Data.NameMap
import Lake.Toml.DateTime

/-!
# TOML Value
-/

open Lean

namespace Lake.Toml

structure NameDict (α : Type u) where
  items : Array (Name × α)
  indices : NameMap Nat
  deriving Inhabited

namespace NameDict

def empty : NameDict α :=
  {items := #[], indices := {}}

instance : EmptyCollection (NameDict α) := ⟨NameDict.empty⟩

def mkEmpty (capacity : Nat) : NameDict α :=
  {items := .mkEmpty capacity, indices := {}}

abbrev size (t : NameDict α) : Nat :=
  t.items.size

def ofArray (items : Array (Name × α)) : NameDict α := Id.run do
  let mut indices := mkNameMap Nat
  for h : i in [0:items.size] do
    indices := indices.insert (items[i]'h.upper).1 i
  return {items, indices}

def findIdx? (k : Name) (t : NameDict α) : Option (Fin t.size) := do
  let i ← t.indices.find? k
  if h : i < t.items.size then some ⟨i, h⟩ else none

def find? (k : Name) (t : NameDict α) : Option α := do
  t.items[← t.findIdx? k]?.map (·.2)

def contains (k : Name) (t : NameDict α) : Bool :=
  t.indices.contains k

def push (k : Name) (v : α) (t : NameDict α) : NameDict α :=
  {items := t.items.push ⟨k,v⟩, indices := t.indices.insert k t.items.size}

def insert (k : Name) (v : α) (t : NameDict α) : NameDict α :=
  if let some i := t.findIdx? k then
    {items := t.items.set i (k, v), indices := t.indices.insert k i}
  else
    t.push k v

def append (self other : NameDict α) : NameDict α :=
  other.items.foldl (fun t (k,v) => t.insert k v) self

instance : Append (NameDict α) := ⟨NameDict.append⟩

protected def beq [BEq α] (self other : NameDict α) : Bool :=
  self.items == other.items

instance [BEq α] : BEq (NameDict α) := ⟨NameDict.beq⟩

protected def toJson [ToJson α] (t : NameDict α) : Json :=
  .obj <| t.items.foldl (init := .leaf) fun m (k,v) =>
    m.insert compare (k.toString (escape := false)) (toJson v)

instance [ToJson α] : ToJson (NameDict α) := ⟨NameDict.toJson⟩

end NameDict

/-- A TOML value. -/
inductive Value
| string (s : String)
| integer (n : Int)
| float (n : Float)
| boolean (b : Bool)
| dateTime (dt : DateTime)
| array (xs : Array Value)
| table (xs : NameDict Value)
deriving Inhabited, BEq

abbrev Table := NameDict Value

instance : Coe String Value := ⟨Value.string⟩
instance : Coe Int Value := ⟨Value.integer⟩
instance : Coe Float Value := ⟨Value.float⟩
instance : Coe Bool Value := ⟨Value.boolean⟩
instance : Coe DateTime Value := ⟨Value.dateTime⟩
instance : Coe (Array Value) Value := ⟨Value.array⟩
instance : Coe Table Value := ⟨Value.table⟩

--------------------------------------------------------------------------------
/-! ## Pretty Printing -/
--------------------------------------------------------------------------------

protected partial def Value.toJson (v : Value) : Json :=
  have : ToJson Value := ⟨Value.toJson⟩
  match v with
  | .string s => toJson s
  | .integer n => toJson n
  | .float n => toJson n
  | .boolean b => toJson b
  | .dateTime dt => toJson dt
  | .array xs => toJson xs
  | .table t => toJson t

instance : ToJson Value := ⟨Value.toJson⟩

partial def hexEncodeAux (n : Nat) (s : String) : String :=
  let r := n / 16
  if r = 0 then
    s
  else
    let d := n % 16
    if d ≤ 9 then
      hexEncodeAux r (s.push <| Char.ofNat <| '0'.val.toNat + d)
    else
      hexEncodeAux r (s.push <| Char.ofNat <| 'A'.val.toNat + (d - 10))

@[inline] def hexEncode (n : Nat) : String :=
  hexEncodeAux n ""

def ppString (s : String) : String :=
  let s := s.foldl (init := "\"") fun s c =>
    match c with
    | '\x08' => s ++ "\\b"
    | '\t' => s ++ "\\t"
    | '\n' => s ++ "\\n"
    | '\x0C' => s ++ "\\f"
    | '\r' => s ++ "\\r"
    | '\"' => s ++ "\\\""
    | '\\' => s ++ "\\\\"
    | _ =>
      if c.val < 0x20 || c.val == 0x7F then
        s ++ "\\U" ++ lpad (hexEncode c.val.toNat) '0' 8
      else
        s.push c
  s.push '\"'

def ppSimpleKey (k : String) : String :=
  if k.all (fun c => c.isAlphanum || c == '_' || c == '-') then
    k
  else
    ppString k

partial def ppKey (k : Name) : String :=
  match k with
  | .str p s =>
    if p.isAnonymous then
      ppSimpleKey s
    else
      s!"{ppKey p}.{ppSimpleKey s}"
  | _ => panic! "invalid TOML key"


mutual

partial def Table.toString (t : Table) : String :=
  have : ToString Value := ⟨Value.toString⟩
  let xs := t.items.map fun (k,v) => s!"{ppKey k} = {v}"
  "{" ++ ", ".intercalate xs.toList ++ "}"

partial def Value.toString (v : Value) : String :=
  have : ToString Value := ⟨Value.toString⟩
  match v with
  | .string s => ppString s
  | .integer n => toString n
  | .float n => toString n
  | .boolean b => toString b
  | .dateTime dt => toString dt
  | .array xs => toString xs.toList
  | .table t => Table.toString t

end

instance : ToString Value := ⟨Value.toString⟩

partial def ppTable (t : Table) : String :=
  t.items.foldl (init := "") fun s (k,v) =>
    match v with
    | .array xs => xs.foldl (init := s) fun s v =>
      match v with
      | .table t => s ++ s!"\n[[{ppKey k}]]\n" ++ Table.toString t
      | _ => appendKeyval s k v
    | .table t =>
      let s := s ++ s!"\n[{ppKey k}]\n"
      t.items.foldl (fun s (k,v) => appendKeyval s k v) s
    | _ => appendKeyval s k v
where
  appendKeyval s k v :=
    s.append s!"{ppKey k} = {v}\n"
