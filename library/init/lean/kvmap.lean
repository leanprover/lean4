/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.name init.data.option.basic

namespace lean

inductive data_value
| of_string (v : string)
| of_nat    (v : nat)
| of_bool   (v : bool)
| of_name   (v : name)

def data_value.beq : data_value → data_value → bool
| (data_value.of_string s₁) (data_value.of_string s₂) := s₁ = s₂
| (data_value.of_nat n₁)    (data_value.of_nat n₂)    := n₂ = n₂
| (data_value.of_bool b₁)   (data_value.of_bool b₂)   := b₁ = b₂
| _                         _                         := ff

instance data_value.has_beq : has_beq data_value := ⟨data_value.beq⟩

/- Remark: we do not use rbmap here because we need to manipulate kvmap objects in
   C++ and rbmap is implemented in Lean. So, we use just a list until we can
   generate C++ code from Lean code. -/
structure kvmap :=
(entries : list (name × data_value) := [])

namespace kvmap
def find_core : list (name × data_value) → name → option data_value
| []         k' := none
| ((k,v)::m) k' := if k = k' then some v else find_core m k'

def find : kvmap → name → option data_value
| ⟨m⟩ k := find_core m k

def insert_core : list (name × data_value) → name → data_value → list (name × data_value)
| []         k' v' := [(k',v')]
| ((k,v)::m) k' v' := if k = k' then (k, v') :: m else (k, v) :: insert_core m k' v'

def insert : kvmap → name → data_value → kvmap
| ⟨m⟩ k v := ⟨insert_core m k v⟩

def contains (m : kvmap) (n : name) : bool :=
(m.find n).is_some

def get_string (m : kvmap) (k : name) : option string :=
match m.find k with
| some (data_value.of_string v) := some v
| _                             := none

def get_nat (m : kvmap) (k : name) : option nat :=
match m.find k with
| some (data_value.of_nat v) := some v
| _                          := none

def get_bool (m : kvmap) (k : name) : option bool :=
match m.find k with
| some (data_value.of_bool v) := some v
| _                           := none

def get_name (m : kvmap) (k : name) : option name :=
match m.find k with
| some (data_value.of_name v) := some v
| _                           := none

def set_string (m : kvmap) (k : name) (v : string) : kvmap :=
m.insert k (data_value.of_string v)

def set_nat (m : kvmap) (k : name) (v : nat) : kvmap :=
m.insert k (data_value.of_nat v)

def set_bool (m : kvmap) (k : name) (v : bool) : kvmap :=
m.insert k (data_value.of_bool v)

def set_name (m : kvmap) (k : name) (v : name) : kvmap :=
m.insert k (data_value.of_name v)

def subset : kvmap → kvmap → bool
| ⟨[]⟩          m₂ := tt
| ⟨(k, v₁)::m₁⟩ m₂ :=
  (match m₂.find k with
   | some v₂ := v₁ == v₂ && subset ⟨m₁⟩ m₂
   | none    := ff)

def eqv (m₁ m₂ : kvmap) : bool :=
subset m₁ m₂ && subset m₂ m₁

instance : has_beq kvmap := ⟨eqv⟩

end kvmap
end lean
