/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lean.Data.NameMap.Basic
import Init.Data.Nat.Fold

/-! # Red-Black Dictionary

Defines an **insertion-ordered** key-value mapping backed by an red-black tree.
Implemented via a key-index `Std.TreeMap` into an `Array` of key-value pairs.
-/

open Lean

namespace Lake.Toml

/- An insertion-ordered key-value mapping backed by a red-black tree. -/
public structure RBDict (α : Type u) (β : Type v) (cmp : α → α → Ordering)  where
  items : Array (α × β)
  indices : Std.TreeMap α Nat cmp
  deriving Inhabited

public abbrev NameDict (α : Type u) := RBDict Name α Name.quickCmp

namespace RBDict

public def empty : RBDict α β cmp :=
  {items := #[], indices := {}}

public instance : EmptyCollection (RBDict α β cmp) := ⟨RBDict.empty⟩

public def mkEmpty (capacity : Nat) : RBDict α β cmp :=
  {items := .mkEmpty capacity, indices := {}}

public def ofArray (items : Array (α × β)) : RBDict α β cmp :=
  let indices := items.size.fold (init := ∅) fun i _ indices =>
    indices.insert items[i].1 i
  {items, indices}

public protected def beq [BEq (α × β)] (self other : RBDict α β cmp) : Bool :=
  self.items == other.items

public instance [BEq (α × β)] : BEq (RBDict α β cmp) := ⟨RBDict.beq⟩

public abbrev size (t : RBDict α β cmp) : Nat :=
  t.items.size

public abbrev isEmpty (t : RBDict α β cmp) : Bool :=
  t.items.isEmpty

public def keys (t : RBDict α β cmp) : Array α :=
  t.items.map (·.1)

public def values (t : RBDict α β cmp) : Array β :=
  t.items.map (·.2)

public def contains (k : α) (t : RBDict α β cmp) : Bool :=
  t.indices.contains k

public def findIdx? (k : α) (t : RBDict α β cmp) : Option (Fin t.size) := do
  let i ← t.indices.get? k; if h : i < t.items.size then some ⟨i, h⟩ else none

public def findEntry? (k : α) (t : RBDict α β cmp) : Option (α × β) := do
  return t.items[← t.findIdx? k]

@[inline] public def find? (k : α) (t : RBDict α β cmp) : Option β := do
  return (← t.findEntry? k).2

public def push (k : α) (v : β) (t : RBDict α β cmp) : RBDict α β cmp :=
  {items := t.items.push ⟨k,v⟩, indices := t.indices.insert k t.items.size}

@[specialize] public def alter (k : α) (f : Option β → β) (t : RBDict α β cmp) : RBDict α β cmp :=
   if let some i := t.findIdx? k then
    {t with items := t.items.modify i fun (k, v) => (k, f (some v))}
  else
    t.push k (f none)

public def insert (k : α) (v : β) (t : RBDict α β cmp) : RBDict α β cmp :=
  if let some i := t.findIdx? k then
    if h : i < t.items.size then
      {t with items := t.items.set i (k,v)}
    else
      t.push k v
  else
    t.push k v

/-- Inserts the value into the dictionary if `p` is `true`. -/
@[macro_inline, expose] public def insertIf (p : Bool) (k : α) (v : β) (t : RBDict α β cmp) : RBDict α β cmp :=
  if p then t.insert k v else t

/-- Inserts the value into the dictionary if `p` is `false`. -/
@[macro_inline, expose] public def insertUnless (p : Bool) (k : α) (v : β) (t : RBDict α β cmp) : RBDict α β cmp :=
  if p then t else t.insert k v

/-- Insert the value into the dictionary if it is not `none`. -/
@[macro_inline, expose] public def insertSome (k : α) (v? : Option β) (t : RBDict α β cmp) : RBDict α β cmp :=
  if let some v := v? then t.insert k v else t

public def appendArray (self : RBDict α β cmp) (other : Array (α × β)): RBDict α β cmp :=
  other.foldl (fun t (k,v) => t.insert k v) self

public instance : HAppend (RBDict α β cmp) (Array (α × β)) (RBDict α β cmp) := ⟨RBDict.appendArray⟩

@[inline] public def append (self other : RBDict α β cmp) : RBDict α β cmp :=
  self.appendArray other.items

public instance : Append (RBDict α β cmp) := ⟨RBDict.append⟩

@[inline] public def map (f : α → β → γ) (t : RBDict α β cmp) : RBDict α γ cmp :=
  {t with items := t.items.map fun ⟨k, v⟩ => ⟨k, f k v⟩}

@[inline] public def filter (p : α → β → Bool) (t : RBDict α β cmp) : RBDict α β cmp :=
  t.items.foldl (init := {}) fun t (k, v) => if p k v then t.push k v else t

@[inline] public def filterMap (f : α → β → Option γ) (t : RBDict α β cmp) : RBDict α γ cmp :=
  t.items.foldl (init := {}) fun t ⟨k, v⟩ => if let some v := f k v then t.push k v else t

@[inline] public def foldM [Monad m] (f : σ → α → β → m σ) (init : σ) (t : RBDict α β cmp) : m σ :=
  t.items.foldlM (init := init) fun s ⟨k, v⟩ => f s k v

@[inline] public def fold (f : σ → α → β → σ) (init : σ) (t : RBDict α β cmp) : σ :=
  Id.run <| t.foldM f init
