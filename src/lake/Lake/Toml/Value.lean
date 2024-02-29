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

abbrev isEmpty (t : NameDict α) : Bool :=
  t.items.isEmpty

def ofArray (items : Array (Name × α)) : NameDict α := Id.run do
  let mut indices := mkNameMap Nat
  for h : i in [0:items.size] do
    indices := indices.insert (items[i]'h.upper).1 i
  return {items, indices}

def keys (t : NameDict α) : Array Name :=
  t.items.map (·.1)

def values (t : NameDict α) : Array α :=
  t.items.map (·.2)

def contains (k : Name) (t : NameDict α) : Bool :=
  t.indices.contains k

def findIdx? (k : Name) (t : NameDict α) : Option (Fin t.size) := do
  let i ← t.indices.find? k
  if h : i < t.items.size then some ⟨i, h⟩ else none

def find? (k : Name) (t : NameDict α) : Option α := do
  t.items[← t.findIdx? k].2

def push (k : Name) (v : α) (t : NameDict α) : NameDict α :=
  {items := t.items.push ⟨k,v⟩, indices := t.indices.insert k t.items.size}

@[specialize] def insertMapM [Monad m] (k : Name) (f : Option α → m α) (t : NameDict α) : m (NameDict α) := do
  if let some i := t.findIdx? k then
    return {t with items := ← t.items.modifyM i fun (k, v) => return (k, ← f (some v))}
  else
    return t.push k (← f none)

@[inline] def insertMap (k : Name) (f : Option α → α) (t : NameDict α) : NameDict α :=
  Id.run <| t.insertMapM k fun v? => pure <| f v?

def insert (k : Name) (v : α) (t : NameDict α) : NameDict α :=
  t.insertMap k fun _ => v

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

def map (f : α → β) (t : NameDict α) : NameDict β :=
  {t with items := t.items.map fun (k, v) => (k, f v)}

def filter (p : α → Bool) (t : NameDict α) : NameDict α :=
  t.items.foldl (init := {}) fun t (k, v) =>
    if p v then t.push k v else t

def filterMap (f : α → Option β) (t : NameDict α) : NameDict β :=
  t.items.foldl (init := {}) fun t (k, v) =>
    if let some v := f v then t.push k v else t

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

instance : OfNat Value n := ⟨.integer n⟩
instance : EmptyCollection Value := ⟨.table {}⟩
instance : Coe String Value := ⟨.string⟩
instance : Coe Int Value := ⟨.integer⟩
instance : Coe Float Value := ⟨.float⟩
instance : Coe Bool Value := ⟨.boolean⟩
instance : Coe DateTime Value := ⟨.dateTime⟩
instance : Coe (Array Value) Value := ⟨.array⟩
instance : Coe Table Value := ⟨.table⟩

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
        s ++ "\\u" ++ lpad (String.mk <| Nat.toDigits 16 c.val.toNat) '0' 4
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
  | _ => ""

mutual

partial def ppInlineTable (t : Table) : String :=
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
  | .table t => ppInlineTable t

end

instance : ToString Value := ⟨Value.toString⟩

def ppTable (t : Table) : String :=
  String.trimLeft <| t.items.foldl (init := "") fun s (k,v) =>
    match v with
    | .array xs => xs.foldl (init := s) fun s v =>
      match v with
      | .table t =>
        let s := s ++ s!"\n[[{ppKey k}]]\n"
        t.items.foldl (fun s (k,v) => appendKeyval s k v) s
      | _ => appendKeyval s k v
    | .table t =>
      let s := s ++ s!"\n[{ppKey k}]\n"
      t.items.foldl (fun s (k,v) => appendKeyval s k v) s
    | _ => appendKeyval s k v
where
  appendKeyval s k v :=
    s.append s!"{ppKey k} = {v}\n"
