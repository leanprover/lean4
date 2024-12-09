/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lean.Data.HashSet
import Std.Data.HashSet.Basic

open Lean

namespace Lake

/-- A `HashSet` that preserves insertion order. -/
structure OrdHashSet (α) [Hashable α] [BEq α] where
  toHashSet : Std.HashSet α
  toArray : Array α

namespace OrdHashSet
variable [Hashable α] [BEq α]

instance : Coe (OrdHashSet α) (Std.HashSet α) := ⟨toHashSet⟩

def empty : OrdHashSet α :=
  ⟨.empty, .empty⟩

instance : EmptyCollection (OrdHashSet α) := ⟨empty⟩

def mkEmpty (size : Nat) : OrdHashSet α :=
  ⟨.empty, .mkEmpty size⟩

def insert (self : OrdHashSet α) (a : α) : OrdHashSet α :=
  if self.toHashSet.contains a then
    self
  else
    ⟨self.toHashSet.insert a, self.toArray.push a⟩

def appendArray (self : OrdHashSet α) (arr : Array α) :=
  arr.foldl (·.insert ·) self

instance : HAppend (OrdHashSet α) (Array α) (OrdHashSet α) := ⟨OrdHashSet.appendArray⟩

protected def append (self other : OrdHashSet α) :=
  self.appendArray other.toArray

instance : Append (OrdHashSet α) := ⟨OrdHashSet.append⟩

def ofArray (arr : Array α) : OrdHashSet α :=
  mkEmpty arr.size |>.appendArray arr

@[inline] def all (f : α → Bool) (self : OrdHashSet α) : Bool  :=
  self.toArray.all f

@[inline] def any (f : α → Bool) (self : OrdHashSet α) : Bool  :=
  self.toArray.any f

@[inline] def foldl (f : β → α → β) (init : β) (self : OrdHashSet α) : β :=
  self.toArray.foldl f init

@[inline] def foldlM [Monad m] (f : β → α → m β) (init : β) (self : OrdHashSet α) : m β :=
  self.toArray.foldlM f init

@[inline] def foldr (f : α → β → β) (init : β) (self : OrdHashSet α) : β :=
  self.toArray.foldr f init

@[inline] def foldrM [Monad m] (f : α → β → m β) (init : β) (self : OrdHashSet α) : m β :=
  self.toArray.foldrM f init

@[inline] def forM [Monad m] (f : α → m PUnit) (self : OrdHashSet α) : m PUnit :=
  self.toArray.forM f

@[inline] protected def forIn [Monad m] (self : OrdHashSet α) (init : β) (f : α → β → m (ForInStep β)) : m β :=
  ForIn.forIn self.toArray init f

instance : ForIn m (OrdHashSet α) α := ⟨OrdHashSet.forIn⟩
