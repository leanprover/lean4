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

structure RBDict (α : Type u) (β : Type v) (cmp : α → α → Ordering)  where
  items : Array (α × β)
  indices : RBMap α Nat cmp
  deriving Inhabited

abbrev NameDict (α : Type u) := RBDict Name α Name.quickCmp

namespace RBDict

def empty : RBDict α β cmp :=
  {items := #[], indices := {}}

instance : EmptyCollection (RBDict α β cmp) := ⟨RBDict.empty⟩

def mkEmpty (capacity : Nat) : RBDict α β cmp :=
  {items := .mkEmpty capacity, indices := {}}

abbrev size (t : RBDict α β cmp) : Nat :=
  t.items.size

abbrev isEmpty (t : RBDict α β cmp) : Bool :=
  t.items.isEmpty

def ofArray (items : Array (α × β)) : RBDict α β cmp := Id.run do
  let mut indices := mkRBMap α Nat cmp
  for h : i in [0:items.size] do
    indices := indices.insert (items[i]'h.upper).1 i
  return {items, indices}

def keys (t : RBDict α β cmp) : Array α :=
  t.items.map (·.1)

def values (t : RBDict α β cmp) : Array β :=
  t.items.map (·.2)

def contains (k : α) (t : RBDict α β cmp) : Bool :=
  t.indices.contains k

def findIdx? (k : α) (t : RBDict α β cmp) : Option (Fin t.size) := do
  let i ← t.indices.find? k
  if h : i < t.items.size then some ⟨i, h⟩ else none

def find? (k : α) (t : RBDict α β cmp) : Option β := do
  t.items[← t.findIdx? k].2

def push (k : α) (v : β) (t : RBDict α β cmp) : RBDict α β cmp :=
  {items := t.items.push ⟨k,v⟩, indices := t.indices.insert k t.items.size}

@[specialize] def insertMapM [Monad m] (k : α) (f : Option β → m β) (t : RBDict α β cmp) : m (RBDict α β cmp) := do
  if let some i := t.findIdx? k then
    return {t with items := ← t.items.modifyM i fun (k, v) => return (k, ← f (some v))}
  else
    return t.push k (← f none)

@[inline] def insertMap (k : α) (f : Option β → β) (t : RBDict α β cmp) : RBDict α β cmp :=
  Id.run <| t.insertMapM k fun v? => pure <| f v?

def insert (k : α) (v : β) (t : RBDict α β cmp) : RBDict α β cmp :=
  t.insertMap k fun _ => v

def append (self other : RBDict α β cmp) : RBDict α β cmp :=
  other.items.foldl (fun t (k,v) => t.insert k v) self

instance : Append (RBDict α β cmp) := ⟨RBDict.append⟩

protected def beq [BEq α] [BEq β] (self other : RBDict α β cmp) : Bool :=
  self.items == other.items

instance [BEq α] [BEq β] : BEq (RBDict α β cmp) := ⟨RBDict.beq⟩

def map (f : β → γ) (t : RBDict α β cmp) : RBDict α γ cmp :=
  {t with items := t.items.map fun (k, v) => (k, f v)}

def filter (p : β → Bool) (t : RBDict α β cmp) : RBDict α β cmp :=
  t.items.foldl (init := {}) fun t (k, v) =>
    if p v then t.push k v else t

def filterMap (f : β → Option γ) (t : RBDict α β cmp) : RBDict α γ cmp :=
  t.items.foldl (init := {}) fun t (k, v) =>
    if let some v := f v then t.push k v else t

end RBDict

/-- A TOML value. -/
inductive Value
| string (s : String)
| integer (n : Int)
| float (n : Float)
| boolean (b : Bool)
| dateTime (dt : DateTime)
| array (xs : Array Value)
| private table' (xs : RBDict Name Value Name.quickCmp)
deriving Inhabited, BEq

abbrev Table := NameDict Value
@[match_pattern] abbrev Value.table (t : Table) := Value.table' t

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
