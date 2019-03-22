/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.name init.data.option.basic init.data.int

namespace Lean

inductive DataValue
| ofString (v : String)
| ofNat    (v : Nat)
| ofBool   (v : Bool)
| ofName   (v : Name)
| ofInt    (v : Int)

def DataValue.beq : DataValue → DataValue → Bool
| (DataValue.ofString s₁) (DataValue.ofString s₂) := s₁ = s₂
| (DataValue.ofNat n₁)    (DataValue.ofNat n₂)    := n₂ = n₂
| (DataValue.ofBool b₁)   (DataValue.ofBool b₂)   := b₁ = b₂
| _                         _                     := false

instance DataValue.HasBeq : HasBeq DataValue := ⟨DataValue.beq⟩

/- Remark: we do not use RBMap here because we need to manipulate KVMap objects in
   C++ and RBMap is implemented in Lean. So, we use just a List until we can
   generate C++ code from Lean code. -/
structure KVMap :=
(entries : List (Name × DataValue) := [])

namespace KVMap
def findCore : List (Name × DataValue) → Name → Option DataValue
| []         k' := none
| ((k,v)::m) k' := if k = k' then some v else findCore m k'

def find : KVMap → Name → Option DataValue
| ⟨m⟩ k := findCore m k

def insertCore : List (Name × DataValue) → Name → DataValue → List (Name × DataValue)
| []         k' v' := [(k',v')]
| ((k,v)::m) k' v' := if k = k' then (k, v') :: m else (k, v) :: insertCore m k' v'

def insert : KVMap → Name → DataValue → KVMap
| ⟨m⟩ k v := ⟨insertCore m k v⟩

def contains (m : KVMap) (n : Name) : Bool :=
(m.find n).isSome

def getString (m : KVMap) (k : Name) : Option String :=
match m.find k with
| some (DataValue.ofString v) := some v
| _                             := none

def getNat (m : KVMap) (k : Name) : Option Nat :=
match m.find k with
| some (DataValue.ofNat v) := some v
| _                          := none

def getInt (m : KVMap) (k : Name) : Option Int :=
match m.find k with
| some (DataValue.ofInt v) := some v
| _                        := none

def getBool (m : KVMap) (k : Name) : Option Bool :=
match m.find k with
| some (DataValue.ofBool v) := some v
| _                           := none

def getName (m : KVMap) (k : Name) : Option Name :=
match m.find k with
| some (DataValue.ofName v) := some v
| _                           := none

def setString (m : KVMap) (k : Name) (v : String) : KVMap :=
m.insert k (DataValue.ofString v)

def setNat (m : KVMap) (k : Name) (v : Nat) : KVMap :=
m.insert k (DataValue.ofNat v)

def setInt (m : KVMap) (k : Name) (v : Int) : KVMap :=
m.insert k (DataValue.ofInt v)

def setBool (m : KVMap) (k : Name) (v : Bool) : KVMap :=
m.insert k (DataValue.ofBool v)

def setName (m : KVMap) (k : Name) (v : Name) : KVMap :=
m.insert k (DataValue.ofName v)

def subset : KVMap → KVMap → Bool
| ⟨[]⟩          m₂ := true
| ⟨(k, v₁)::m₁⟩ m₂ :=
  (match m₂.find k with
   | some v₂ := v₁ == v₂ && subset ⟨m₁⟩ m₂
   | none    := false)

def eqv (m₁ m₂ : KVMap) : Bool :=
subset m₁ m₂ && subset m₂ m₁

instance : HasBeq KVMap := ⟨eqv⟩

end KVMap
end Lean
