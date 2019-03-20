/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.name init.data.option.basic

namespace lean

inductive dataValue
| ofString (v : string)
| ofNat    (v : nat)
| ofBool   (v : bool)
| ofName   (v : name)

def dataValue.beq : dataValue → dataValue → bool
| (dataValue.ofString s₁) (dataValue.ofString s₂) := s₁ = s₂
| (dataValue.ofNat n₁)    (dataValue.ofNat n₂)    := n₂ = n₂
| (dataValue.ofBool b₁)   (dataValue.ofBool b₂)   := b₁ = b₂
| _                         _                         := ff

instance dataValue.hasBeq : hasBeq dataValue := ⟨dataValue.beq⟩

/- Remark: we do not use rbmap here because we need to manipulate kvmap objects in
   C++ and rbmap is implemented in Lean. So, we use just a list until we can
   generate C++ code from Lean code. -/
structure kvmap :=
(entries : list (name × dataValue) := [])

namespace kvmap
def findCore : list (name × dataValue) → name → option dataValue
| []         k' := none
| ((k,v)::m) k' := if k = k' then some v else findCore m k'

def find : kvmap → name → option dataValue
| ⟨m⟩ k := findCore m k

def insertCore : list (name × dataValue) → name → dataValue → list (name × dataValue)
| []         k' v' := [(k',v')]
| ((k,v)::m) k' v' := if k = k' then (k, v') :: m else (k, v) :: insertCore m k' v'

def insert : kvmap → name → dataValue → kvmap
| ⟨m⟩ k v := ⟨insertCore m k v⟩

def contains (m : kvmap) (n : name) : bool :=
(m.find n).isSome

def getString (m : kvmap) (k : name) : option string :=
match m.find k with
| some (dataValue.ofString v) := some v
| _                             := none

def getNat (m : kvmap) (k : name) : option nat :=
match m.find k with
| some (dataValue.ofNat v) := some v
| _                          := none

def getBool (m : kvmap) (k : name) : option bool :=
match m.find k with
| some (dataValue.ofBool v) := some v
| _                           := none

def getName (m : kvmap) (k : name) : option name :=
match m.find k with
| some (dataValue.ofName v) := some v
| _                           := none

def setString (m : kvmap) (k : name) (v : string) : kvmap :=
m.insert k (dataValue.ofString v)

def setNat (m : kvmap) (k : name) (v : nat) : kvmap :=
m.insert k (dataValue.ofNat v)

def setBool (m : kvmap) (k : name) (v : bool) : kvmap :=
m.insert k (dataValue.ofBool v)

def setName (m : kvmap) (k : name) (v : name) : kvmap :=
m.insert k (dataValue.ofName v)

def subset : kvmap → kvmap → bool
| ⟨[]⟩          m₂ := tt
| ⟨(k, v₁)::m₁⟩ m₂ :=
  (match m₂.find k with
   | some v₂ := v₁ == v₂ && subset ⟨m₁⟩ m₂
   | none    := ff)

def eqv (m₁ m₂ : kvmap) : bool :=
subset m₁ m₂ && subset m₂ m₁

instance : hasBeq kvmap := ⟨eqv⟩

end kvmap
end lean
