/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

vectors as list subtype
-/
import logic data.list data.subtype algebra.function
open nat list subtype function

definition vec [reducible] (A : Type) (n : nat) := {l : list A | length l = n}

namespace vec
  variables {A B C : Type}

  definition nil : vec A 0 :=
  tag [] rfl

  lemma length_succ {n : nat} {l : list A} (a : A) : length l = n → length (a::l) = succ n :=
  λ h, congr_arg succ h

  definition cons {n : nat} : A → vec A n → vec A (succ n)
  | a (tag v h) := tag (a::v) (length_succ a h)

  notation a :: b := cons a b

  protected definition is_inhabited [instance] [h : inhabited A] : ∀ (n : nat), inhabited (vec A n)
  | 0        := inhabited.mk nil
  | (succ n) := inhabited.mk (inhabited.value h :: inhabited.value (is_inhabited n))

  theorem vec0_eq_nil : ∀ (v : vec A 0), v = nil
  | (tag []     h) := rfl
  | (tag (a::l) h) := by contradiction

  definition head {n : nat} : vec A (succ n) → A
  | (tag []     h) := by contradiction
  | (tag (a::v) h) := a

  definition tail {n : nat} : vec A (succ n) → vec A n
  | (tag []     h) := by contradiction
  | (tag (a::v) h) := tag v (succ.inj h)

  theorem head_cons {n : nat} (a : A) (v : vec A n) : head (a :: v) = a :=
  by induction v; reflexivity

  theorem tail_cons {n : nat} (a : A) (v : vec A n) : tail (a :: v) = v :=
  by induction v; reflexivity

  theorem head_lcons {n : nat} (a : A) (l : list A) (h : length (a::l) = succ n) : head (tag (a::l) h) = a :=
  rfl

  theorem tail_lcons {n : nat} (a : A) (l : list A) (h : length (a::l) = succ n) : tail (tag (a::l) h) = tag l (succ.inj h) :=
  rfl

  theorem eta : ∀ {n : nat} (v : vec A (succ n)), head v :: tail v = v
  | 0     (tag [] h)     := by contradiction
  | 0     (tag (a::l) h) := rfl
  | (n+1) (tag [] h)     := by contradiction
  | (n+1) (tag (a::l) h) := rfl

  definition mem {n : nat} (a : A) (v : vec A n) : Prop :=
  a ∈ elt_of v

  definition last {n : nat} : vec A (succ n) → A
  | (tag l h) := list.last l (ne_nil_of_length_eq_succ h)

  definition map {n : nat} (f : A → B) : vec A n → vec B n
  | (tag l h) := tag (list.map f l) (by clear map; substvars; rewrite length_map)

  theorem map_nil (f : A → B) : map f nil = nil :=
  rfl

  theorem map_cons {n : nat} (f : A → B) (a : A) (v : vec A n) : map f (a::v) = f a :: map f v :=
  by induction v; reflexivity

  theorem map_tag {n : nat} (f : A → B) (l : list A) (h : length l = n)
                   : map f (tag l h) = tag (list.map f l) (by substvars; rewrite length_map) :=
  by reflexivity

  theorem map_map {n : nat} (g : B → C) (f : A → B) (v : vec A n) : map g (map f v) = map (g ∘ f) v :=
  begin cases v, rewrite *map_tag, apply subtype.eq, apply list.map_map end

end vec
