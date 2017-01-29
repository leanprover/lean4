/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/
prelude
import init.data.ordering init.function init.meta.name init.meta.format

meta constant {u₁ u₂} rb_map : Type u₁ → Type u₂ → Type (max u₁ u₂)

namespace rb_map
meta constant mk_core {key : Type} (data : Type)        : (key → key → ordering) → rb_map key data
meta constant size {key : Type} {data : Type}           : rb_map key data → nat
meta constant insert {key : Type} {data : Type}         : rb_map key data → key → data → rb_map key data
meta constant erase  {key : Type} {data : Type}         : rb_map key data → key → rb_map key data
meta constant contains {key : Type} {data : Type}       : rb_map key data → key → bool
meta constant find {key : Type} {data : Type}           : rb_map key data → key → option data
meta constant min {key : Type} {data : Type}            : rb_map key data → option data
meta constant max {key : Type} {data : Type}            : rb_map key data → option data
meta constant fold {key : Type} {data : Type} {α :Type} : rb_map key data → α → (key → data → α → α) → α

attribute [inline]
meta def mk (key : Type) [has_ordering key] (data : Type) : rb_map key data :=
mk_core data has_ordering.cmp

open list
meta def of_list {key : Type} {data : Type} [has_ordering key] : list (key × data) → rb_map key data
| []           := mk key data
| ((k, v)::ls) := insert (of_list ls) k v

meta def keys {key : Type} {data : Type} (m : rb_map key data) : list key :=
fold m [] (λk v ks, k :: ks)

meta def values {key : Type} {data : Type} (m : rb_map key data) : list data :=
fold m [] (λk v vs, v :: vs)

meta def to_list {key : Type} {data : Type} (m : rb_map key data) : list (key × data) :=
fold m [] (λk v res, (k, v) :: res)

meta def set_of_list {A} [has_ordering A] : list A → rb_map A unit
| []      := mk _ _
| (x::xs) := insert (set_of_list xs) x ()

meta def map {A B C} [has_ordering A] (f : B → C) (m : rb_map A B) : rb_map A C :=
fold m (mk _ _) (λk v res, insert res k (f v))

meta def for {A B C} [has_ordering A] (m : rb_map A B) (f : B → C) : rb_map A C :=
map f m

meta def filter {A B} [has_ordering A] (m : rb_map A B) (f : B → Prop) [decidable_pred f] :=
fold m (mk _ _) $ λa b m', if f b then insert m' a b else m'

end rb_map

attribute [reducible]
meta def nat_map (data : Type) := rb_map nat data
namespace nat_map
  export rb_map (hiding mk)

  attribute [inline]
  meta def mk (data : Type) : nat_map data :=
  rb_map.mk nat data
end nat_map

attribute [reducible]
meta def name_map (data : Type) := rb_map name data
namespace name_map
  export rb_map (hiding mk)

  attribute [inline]
  meta def mk (data : Type) : name_map data :=
  rb_map.mk name data
end name_map

open rb_map prod
section
open format
variables {key : Type} {data : Type} [has_to_format key] [has_to_format data]
private meta def format_key_data (k : key) (d : data) (first : bool) : format :=
(if first then to_fmt "" else to_fmt "," ++ line) ++ to_fmt k ++ space ++ to_fmt "←" ++ space ++ to_fmt d

meta instance : has_to_format (rb_map key data) :=
⟨λ m, group $ to_fmt "⟨" ++ nest 1 (fst (fold m (to_fmt "", tt) (λ k d p, (fst p ++ format_key_data k d (snd p), ff)))) ++
              to_fmt "⟩"⟩
end

section
variables {key : Type} {data : Type} [has_to_string key] [has_to_string data]
private meta def key_data_to_string (k : key) (d : data) (first : bool) : string :=
(if first then "" else ", ") ++ to_string k ++ " ← " ++ to_string d

meta instance : has_to_string (rb_map key data) :=
⟨λ m, "⟨" ++ (fst (fold m ("", tt) (λ k d p, (fst p ++ key_data_to_string k d (snd p), ff)))) ++ "⟩"⟩
end

/- a variant of rb_maps that stores a list of elements for each key.
   "find" returns the list of elements in the opposite order that they were inserted. -/

meta def rb_lmap (key : Type) (data : Type) : Type := rb_map key (list data)

namespace rb_lmap

protected meta def mk (key : Type) [has_ordering key] (data : Type) : rb_lmap key data :=
rb_map.mk key (list data)

meta def insert {key : Type} {data : Type} (rbl : rb_lmap key data) (k : key) (d : data) :
  rb_lmap key data :=
match (rb_map.find rbl k) with
| none     := rb_map.insert rbl k [d]
| (some l) := rb_map.insert (rb_map.erase rbl k) k (d :: l)
end

meta def erase {key : Type} {data : Type} (rbl : rb_lmap key data) (k : key) :
  rb_lmap key data :=
rb_map.erase rbl k

meta def contains {key : Type} {data : Type} (rbl : rb_lmap key data) (k : key) : bool :=
rb_map.contains rbl k

meta def find {key : Type} {data : Type} (rbl : rb_lmap key data) (k : key) : list data :=
match (rb_map.find rbl k) with
| none     := []
| (some l) := l
end

end rb_lmap
