/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.name init.data.option.basic

namespace Lean

inductive DataValue
| ofString (v : String)
| ofNat    (v : Nat)
| ofBool   (v : Bool)
| ofName   (v : Name)

def DataValue.beq : DataValue → DataValue → Bool
| (DataValue.ofString s₁) (DataValue.ofString s₂) := s₁ = s₂
| (DataValue.ofNat n₁)    (DataValue.ofNat n₂)    := n₂ = n₂
| (DataValue.ofBool b₁)   (DataValue.ofBool b₂)   := b₁ = b₂
| _                         _                         := ff

instance DataValue.HasBeq : HasBeq DataValue := ⟨DataValue.beq⟩

/- Remark: we do not use Rbmap here because we need to manipulate Kvmap objects in
   C++ and Rbmap is implemented in Lean. So, we use just a List until we can
   generate C++ code from Lean code. -/
structure Kvmap :=
(entries : List (Name × DataValue) := [])

namespace Kvmap
def findCore : List (Name × DataValue) → Name → Option DataValue
| []         k' := none
| ((k,v)::m) k' := if k = k' then some v else findCore m k'

def find : Kvmap → Name → Option DataValue
| ⟨m⟩ k := findCore m k

def insertCore : List (Name × DataValue) → Name → DataValue → List (Name × DataValue)
| []         k' v' := [(k',v')]
| ((k,v)::m) k' v' := if k = k' then (k, v') :: m else (k, v) :: insertCore m k' v'

def insert : Kvmap → Name → DataValue → Kvmap
| ⟨m⟩ k v := ⟨insertCore m k v⟩

def contains (m : Kvmap) (n : Name) : Bool :=
(m.find n).isSome

def getString (m : Kvmap) (k : Name) : Option String :=
match m.find k with
| some (DataValue.ofString v) := some v
| _                             := none

def getNat (m : Kvmap) (k : Name) : Option Nat :=
match m.find k with
| some (DataValue.ofNat v) := some v
| _                          := none

def getBool (m : Kvmap) (k : Name) : Option Bool :=
match m.find k with
| some (DataValue.ofBool v) := some v
| _                           := none

def getName (m : Kvmap) (k : Name) : Option Name :=
match m.find k with
| some (DataValue.ofName v) := some v
| _                           := none

def setString (m : Kvmap) (k : Name) (v : String) : Kvmap :=
m.insert k (DataValue.ofString v)

def setNat (m : Kvmap) (k : Name) (v : Nat) : Kvmap :=
m.insert k (DataValue.ofNat v)

def setBool (m : Kvmap) (k : Name) (v : Bool) : Kvmap :=
m.insert k (DataValue.ofBool v)

def setName (m : Kvmap) (k : Name) (v : Name) : Kvmap :=
m.insert k (DataValue.ofName v)

def subset : Kvmap → Kvmap → Bool
| ⟨[]⟩          m₂ := tt
| ⟨(k, v₁)::m₁⟩ m₂ :=
  (match m₂.find k with
   | some v₂ := v₁ == v₂ && subset ⟨m₁⟩ m₂
   | none    := ff)

def eqv (m₁ m₂ : Kvmap) : Bool :=
subset m₁ m₂ && subset m₂ m₁

instance : HasBeq Kvmap := ⟨eqv⟩

end Kvmap
end Lean
