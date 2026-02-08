/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Std.Data.HashSet.Basic

open Lean

namespace Lake

/-- A `HashSet` that preserves insertion order. -/
public structure OrdHashSet (α) [Hashable α] [BEq α] where
  toHashSet : Std.HashSet α
  toArray : Array α

namespace OrdHashSet
variable [Hashable α] [BEq α]

public instance : Coe (OrdHashSet α) (Std.HashSet α) := ⟨toHashSet⟩

public def empty : OrdHashSet α :=
  ⟨∅, .empty⟩

public instance : EmptyCollection (OrdHashSet α) := ⟨empty⟩

public def mkEmpty (size : Nat) : OrdHashSet α :=
  ⟨∅, .mkEmpty size⟩

public def insert (self : OrdHashSet α) (a : α) : OrdHashSet α :=
  if self.toHashSet.contains a then
    self
  else
    ⟨self.toHashSet.insert a, self.toArray.push a⟩

public def appendArray (self : OrdHashSet α) (arr : Array α) :=
  arr.foldl (·.insert ·) self

public instance : HAppend (OrdHashSet α) (Array α) (OrdHashSet α) := ⟨OrdHashSet.appendArray⟩

public protected def append (self other : OrdHashSet α) :=
  self.appendArray other.toArray

public instance : Append (OrdHashSet α) := ⟨OrdHashSet.append⟩

public def ofArray (arr : Array α) : OrdHashSet α :=
  mkEmpty arr.size |>.appendArray arr

@[inline] public def all (f : α → Bool) (self : OrdHashSet α) : Bool  :=
  self.toArray.all f

@[inline] public def any (f : α → Bool) (self : OrdHashSet α) : Bool  :=
  self.toArray.any f

@[inline] public def foldl (f : β → α → β) (init : β) (self : OrdHashSet α) : β :=
  self.toArray.foldl f init

@[inline] public def foldlM [Monad m] (f : β → α → m β) (init : β) (self : OrdHashSet α) : m β :=
  self.toArray.foldlM f init

@[inline] public def foldr (f : α → β → β) (init : β) (self : OrdHashSet α) : β :=
  self.toArray.foldr f init

@[inline] public def foldrM [Monad m] (f : α → β → m β) (init : β) (self : OrdHashSet α) : m β :=
  self.toArray.foldrM f init

@[inline] public def forM [Monad m] (f : α → m PUnit) (self : OrdHashSet α) : m PUnit :=
  self.toArray.forM f

@[inline] public protected def forIn [Monad m] (self : OrdHashSet α) (init : β) (f : α → β → m (ForInStep β)) : m β :=
  ForIn.forIn self.toArray init f

public instance [Monad m] : ForIn m (OrdHashSet α) α := ⟨OrdHashSet.forIn⟩
