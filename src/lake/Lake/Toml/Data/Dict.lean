/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Data.NameMap

/-! # Red-Black Dictionary

Defines an **insertion-ordered** key-value mapping backed by an red-black tree.
Implemented via a key-index `RBMap` into an `Array` of key-value pairs.
-/

open Lean

namespace Lake.Toml

/- An insertion-ordered key-value mapping backed by a red-black tree. -/
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

def ofArray (items : Array (α × β)) : RBDict α β cmp := Id.run do
  let mut indices := mkRBMap α Nat cmp
  for h : i in [0:items.size] do
    indices := indices.insert (items[i]'h.upper).1 i
  return {items, indices}

protected def beq [BEq (α × β)] (self other : RBDict α β cmp) : Bool :=
  self.items == other.items

instance [BEq (α × β)] : BEq (RBDict α β cmp) := ⟨RBDict.beq⟩

abbrev size (t : RBDict α β cmp) : Nat :=
  t.items.size

abbrev isEmpty (t : RBDict α β cmp) : Bool :=
  t.items.isEmpty

def keys (t : RBDict α β cmp) : Array α :=
  t.items.map (·.1)

def values (t : RBDict α β cmp) : Array β :=
  t.items.map (·.2)

def contains (k : α) (t : RBDict α β cmp) : Bool :=
  t.indices.contains k

def findIdx? (k : α) (t : RBDict α β cmp) : Option (Fin t.size) := do
  let i ← t.indices.find? k; if h : i < t.items.size then some ⟨i, h⟩ else none

def findEntry? (k : α) (t : RBDict α β cmp) : Option (α × β) := do
  return t.items[← t.findIdx? k]

@[inline] def find? (k : α) (t : RBDict α β cmp) : Option β := do
  return (← t.findEntry? k).2

def push (k : α) (v : β) (t : RBDict α β cmp) : RBDict α β cmp :=
  {items := t.items.push ⟨k,v⟩, indices := t.indices.insert k t.items.size}

@[specialize] def alter (k : α) (f : Option β → β) (t : RBDict α β cmp) : RBDict α β cmp :=
   if let some i := t.findIdx? k then
    {t with items := t.items.modify i fun (k, v) => (k, f (some v))}
  else
    t.push k (f none)

def insert (k : α) (v : β) (t : RBDict α β cmp) : RBDict α β cmp :=
  if let some i := t.findIdx? k then
    if h : i < t.items.size then
      {t with items := t.items.set i (k,v)}
    else
      t.push k v
  else
    t.push k v

/-- Inserts the value into the dictionary if `p` is `true`. -/
@[macro_inline] def insertIf (p : Bool) (k : α) (v : β) (t : RBDict α β cmp) : RBDict α β cmp :=
  if p then t.insert k v else t

/-- Inserts the value into the dictionary if `p` is `false`. -/
@[macro_inline] def insertUnless (p : Bool) (k : α) (v : β) (t : RBDict α β cmp) : RBDict α β cmp :=
  if p then t else t.insert k v

/-- Insert the value into the dictionary if it is not `none`. -/
@[macro_inline] def insertSome (k : α) (v? : Option β) (t : RBDict α β cmp) : RBDict α β cmp :=
  if let some v := v? then t.insert k v else t

def appendArray (self : RBDict α β cmp) (other : Array (α × β)): RBDict α β cmp :=
  other.foldl (fun t (k,v) => t.insert k v) self

instance : HAppend (RBDict α β cmp) (Array (α × β)) (RBDict α β cmp) := ⟨RBDict.appendArray⟩

@[inline] def append (self other : RBDict α β cmp) : RBDict α β cmp :=
  self.appendArray other.items

instance : Append (RBDict α β cmp) := ⟨RBDict.append⟩

@[inline] def map (f : α → β → γ) (t : RBDict α β cmp) : RBDict α γ cmp :=
  {t with items := t.items.map fun ⟨k, v⟩ => ⟨k, f k v⟩}

@[inline] def filter (p : α → β → Bool) (t : RBDict α β cmp) : RBDict α β cmp :=
  t.items.foldl (init := {}) fun t (k, v) => if p k v then t.push k v else t

@[inline] def filterMap (f : α → β → Option γ) (t : RBDict α β cmp) : RBDict α γ cmp :=
  t.items.foldl (init := {}) fun t ⟨k, v⟩ => if let some v := f k v then t.push k v else t
