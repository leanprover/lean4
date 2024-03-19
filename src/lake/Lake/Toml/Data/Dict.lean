/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Data.NameMap

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

/-- Inserts the value into the dictionary if `p` is `true`. -/
@[macro_inline] def insertIf (p : Bool) (k : α) (v : β) (t : RBDict α β cmp) : RBDict α β cmp :=
  if p then t.insert k v else t

/-- Inserts the value into the dictionary if `p` is `false`. -/
@[macro_inline] def insertUnless (p : Bool) (k : α) (v : β) (t : RBDict α β cmp) : RBDict α β cmp :=
  if p then t else t.insert k v

/-- Insert the value into the dictionary if it is not `none`. -/
@[macro_inline] def insertSome (k : α) (v? : Option β) (t : RBDict α β cmp) : RBDict α β cmp :=
  if let some v := v? then t.insert k v else t

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
