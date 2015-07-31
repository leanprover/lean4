/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

vectors as list subtype
-/
import logic data.list data.subtype data.fin
open nat list subtype function

definition vec [reducible] (A : Type) (n : nat) := {l : list A | length l = n}

namespace vec
  variables {A B C : Type}

  theorem induction_on [recursor 4] {P : ∀ {n}, vec A n → Prop} : ∀ {n} (v : vec A n), (∀ (l : list A) {n : nat} (h : length l = n), P (tag l h)) → P v
  | n (tag l h) H := @H l n h

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

  protected definition has_decidable_eq [instance] [h : decidable_eq A] : ∀ (n : nat), decidable_eq (vec A n) :=
  _

  definition of_list (l : list A) : vec A (list.length l) :=
  tag l rfl

  definition to_list {n : nat} : vec A n → list A
  | (tag l h) := l

  theorem to_list_of_list (l : list A) : to_list (of_list l) = l :=
  rfl

  theorem to_list_nil : to_list nil = ([] : list A) :=
  rfl

  theorem length_to_list {n : nat} : ∀ (v : vec A n), list.length (to_list v) = n
  | (tag l h) := h

  theorem heq_of_list_eq {n m} : ∀ {v₁ : vec A n} {v₂ : vec A m}, to_list v₁ = to_list v₂ → n = m → v₁ == v₂
  | (tag l₁ h₁) (tag l₂ h₂) e₁ e₂ := begin
      clear heq_of_list_eq,
      subst e₂, subst h₁,
      unfold to_list at e₁,
      subst l₁
    end

  theorem list_eq_of_heq {n m} {v₁ : vec A n} {v₂ : vec A m} : v₁ == v₂ → n = m → to_list v₁ = to_list v₂ :=
  begin
    intro h₁ h₂, revert v₁ v₂ h₁,
    subst n, intro v₁ v₂ h₁, rewrite [heq.to_eq h₁]
  end

  theorem of_list_to_list {n : nat} (v : vec A n) : of_list (to_list v) == v :=
  begin
    apply heq_of_list_eq, rewrite to_list_of_list, rewrite length_to_list
  end

  definition append {n m : nat} : vec A n → vec A m → vec A (n + m)
  | (tag l₁ h₁) (tag l₂ h₂) := tag (list.append l₁ l₂) (by rewrite [length_append, h₁, h₂])

  infix ++ := append

  open eq.ops

  lemma push_eq_rec : ∀ {n m : nat} {l : list A} (h₁ : n = m) (h₂ : length l = n), h₁ ▹ (tag l h₂) = tag l (h₁ ▹ h₂)
  | n n l (eq.refl n) h₂ := rfl

  theorem append_nil_right {n : nat} (v : vec A n) : v ++ nil = v :=
  induction_on v (λ l n h, by unfold [vec.append, vec.nil]; congruence; apply list.append_nil_right)

  theorem append_nil_left {n : nat} (v : vec A n) : !zero_add ▹ (nil ++ v) = v :=
  induction_on v (λ l n h, begin unfold [vec.append, vec.nil], rewrite [push_eq_rec] end)

  theorem append_nil_left_heq {n : nat} (v : vec A n) : nil ++ v == v :=
  heq_of_eq_rec_left !zero_add (append_nil_left v)

  theorem append.assoc {n₁ n₂ n₃} : ∀ (v₁ : vec A n₁) (v₂ : vec A n₂) (v₃ : vec A n₃), !add.assoc ▹ ((v₁ ++ v₂) ++ v₃) = v₁ ++ (v₂ ++ v₃)
  | (tag l₁ h₁) (tag l₂ h₂) (tag l₃ h₃) := begin
    unfold vec.append, rewrite push_eq_rec,
    congruence,
    apply list.append.assoc
  end

  theorem append.assoc_heq {n₁ n₂ n₃} (v₁ : vec A n₁) (v₂ : vec A n₂) (v₃ : vec A n₃) : (v₁ ++ v₂) ++ v₃ == v₁ ++ (v₂ ++ v₃) :=
  heq_of_eq_rec_left !add.assoc (append.assoc v₁ v₂ v₃)

  definition reverse {n : nat} : vec A n → vec A n
  | (tag l h) := tag (list.reverse l) (by rewrite [length_reverse, h])

  theorem reverse_reverse {n : nat} (v : vec A n) : reverse (reverse v) = v :=
  induction_on v (λ l n h, begin unfold reverse, congruence, apply list.reverse_reverse end)

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

  notation e ∈ s := mem e s
  notation e ∉ s := ¬ e ∈ s

  theorem not_mem_nil (a : A) : a ∉ nil :=
  list.not_mem_nil a

  theorem mem_cons [simp] {n : nat} (a : A) (v : vec A n) : a ∈ a :: v :=
  induction_on v (λ l n h, !list.mem_cons)

  theorem mem_cons_of_mem {n : nat} (y : A) {x : A} {v : vec A n} : x ∈ v → x ∈ y :: v :=
  induction_on v (λ l n h₁ h₂, list.mem_cons_of_mem y h₂)

  theorem eq_or_mem_of_mem_cons {n : nat} {x y : A} {v : vec A n} : x ∈ y::v → x = y ∨ x ∈ v :=
  induction_on v (λ l n h₁ h₂, eq_or_mem_of_mem_cons h₂)

  theorem mem_singleton {n : nat} {x a : A} : x ∈ (a::nil : vec A 1) → x = a :=
  assume h, list.mem_singleton h

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

  open fin

  definition ith {n : nat} : vec A n → fin n → A
  | (tag l h₁) (mk i h₂) := list.ith l i (by rewrite h₁; exact h₂)

  lemma ith_zero {n : nat} (a : A) (v : vec A n) (h : 0 < succ n) : ith (a::v) (mk 0 h) = a :=
  by induction v; reflexivity

  lemma ith_fin_zero {n : nat} (a : A) (v : vec A n) : ith (a::v) (zero n) = a :=
  by unfold zero; apply ith_zero

  lemma ith_succ {n : nat} (a : A) (v : vec A n) (i : nat) (h : succ i < succ n)
                 : ith (a::v) (mk (succ i) h) = ith v (mk_pred i h) :=
  by induction v; reflexivity

  lemma ith_fin_succ {n : nat} (a : A) (v : vec A n) (i : fin n)
                     : ith (a::v) (succ i) = ith v i :=
  begin cases i, unfold fin.succ, rewrite ith_succ end

  lemma ith_zero_eq_head {n : nat} (v : vec A (nat.succ n)) : ith v (zero n) = head v :=
  by rewrite [-eta v, ith_fin_zero, head_cons]

  lemma ith_succ_eq_ith_tail {n : nat} (v : vec A (nat.succ n)) (i : fin n) : ith v (succ i) = ith (tail v) i :=
  by rewrite [-eta v, ith_fin_succ, tail_cons]

  protected lemma ext {n : nat} (v₁ v₂ : vec A n) (h : ∀ i : fin n, ith v₁ i = ith v₂ i) : v₁ = v₂ :=
  begin
    induction n with n ih,
      rewrite [vec0_eq_nil v₁, vec0_eq_nil v₂],
      rewrite [-eta v₁, -eta v₂], congruence,
        show head v₁ = head v₂, by rewrite [-ith_zero_eq_head, -ith_zero_eq_head]; apply h,
        have ∀ i : fin n, ith (tail v₁) i = ith (tail v₂) i, from
          take i, by rewrite [-ith_succ_eq_ith_tail, -ith_succ_eq_ith_tail]; apply h,
        show tail v₁ = tail v₂, from ih _ _ this
  end

  definition tabulate : Π {n : nat}, (fin n → A) → vec A n
  | 0     f := nil
  | (n+1) f := f (@zero n) :: tabulate (λ i : fin n, f (succ i))

  theorem ith_tabulate {n : nat} (f : fin n → A) (i : fin n) : ith (tabulate f) i = f i :=
  begin
    induction n with n ih,
      apply elim0 i,
      cases i with v hlt, cases v,
        {unfold tabulate, rewrite ith_zero},
        {unfold tabulate, rewrite [ith_succ, ih]}
  end
end vec
