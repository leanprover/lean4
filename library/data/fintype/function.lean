/-
Copyright (c) 2015 Haitao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author : Haitao Zhang
-/
import data

open nat function eq.ops

namespace list
-- this is in preparation for counting the number of finite functions
section list_of_lists
open prod
variable {A : Type}

definition cons_pair (pr : A × list A) := (pr1 pr) :: (pr2 pr)

definition cons_all_of (elts : list A) (ls : list (list A)) : list (list A) :=
           map cons_pair (product elts ls)

lemma pair_of_cons {a} {l} {pr : A × list A} : cons_pair pr = a::l → pr = (a, l) :=
      prod.destruct pr (λ p1 p2, assume Peq, list.no_confusion Peq (by intros; substvars))

lemma cons_pair_inj : injective (@cons_pair A) :=
      take p1 p2, assume Pl,
      prod.eq (list.no_confusion Pl (λ P1 P2, P1)) (list.no_confusion Pl (λ P1 P2, P2))

lemma nodup_of_cons_all {elts : list A} {ls : list (list A)}
      : nodup elts → nodup ls → nodup (cons_all_of elts ls) :=
      assume Pelts Pls,
      nodup_map cons_pair_inj (nodup_product Pelts Pls)

lemma length_cons_all {elts : list A} {ls : list (list A)} :
      length (cons_all_of elts ls) = length elts * length ls := calc
      length (cons_all_of elts ls) = length (product elts ls) : length_map
                               ... = length elts * length ls : length_product

variable [finA : fintype A]
include finA

definition all_lists_of_len : ∀ (n : nat), list (list A)
| 0        := [[]]
| (succ n) := cons_all_of (elements_of A) (all_lists_of_len n)

lemma nodup_all_lists : ∀ (n : nat), nodup (@all_lists_of_len A _ n)
| 0                   := nodup_singleton []
| (succ n)            := nodup_of_cons_all (fintype.unique A) (nodup_all_lists n)

lemma mem_all_lists : ∀ (n : nat) (l : list A), length l = n → l ∈ all_lists_of_len n
| 0 []              := assume P, mem_cons [] []
| 0 (a::l)          := assume Peq, by contradiction
| (succ n) []       := assume Peq, by contradiction
| (succ n) (a::l)   := assume Peq, begin
                    apply mem_map, apply mem_product,
                      exact fintype.complete a,
                      exact mem_all_lists n l (succ_inj Peq)
                    end

lemma leq_of_mem_all_lists : ∀ {n : nat} ⦃l : list A⦄,
                           l ∈ all_lists_of_len n → length l = n
| 0 []             := assume P, rfl
| 0 (a::l)         := assume Pin, assert Peq : (a::l) = [], from mem_singleton Pin,
                   by contradiction
| (succ n) []      := assume Pin, obtain pr Pprin Ppr, from exists_of_mem_map Pin,
                   by contradiction
| (succ n) (a::l)  := assume Pin, obtain pr Pprin Ppr, from exists_of_mem_map Pin,
                   assert Pl : l ∈ all_lists_of_len n,
                     from mem_of_mem_product_right ((pair_of_cons Ppr) ▸ Pprin),
                   by rewrite [length_cons, leq_of_mem_all_lists Pl]

open fintype
lemma length_all_lists : ∀ {n : nat}, length (@all_lists_of_len A _ n) = (card A) ^ n
| 0         := calc length [[]] = 1 : length_cons
| (succ n)  := calc length _ = card A * length (all_lists_of_len n) : length_cons_all
                         ... = card A * (card A ^ n) : length_all_lists
                         ... = (card A ^ n) * card A : nat.mul.comm
                         ... = (card A) ^ (succ n) : pow_succ

end list_of_lists

section kth

variable {A : Type}

definition kth : ∀ k (l : list A), k < length l → A
| k []        := begin rewrite length_nil, intro Pltz, exact absurd Pltz !not_lt_zero end
| 0 (a::l)    := λ P, a
| (k+1) (a::l):= by rewrite length_cons; intro Plt; exact kth k l (lt_of_succ_lt_succ Plt)

lemma kth_zero_of_cons {a} (l : list A) (P : 0 < length (a::l)) : kth 0 (a::l) P = a :=
      rfl
lemma kth_succ_of_cons {a} k (l : list A) (P : k+1 < length (a::l)) :
      kth (succ k) (a::l) P = kth k l (lt_of_succ_lt_succ P) :=
      rfl

lemma kth_mem : ∀ {k : nat} {l : list A} P, kth k l P ∈ l
| k []            := assume P, absurd P !not_lt_zero
| 0 (a::l)        := assume P, by rewrite kth_zero_of_cons; apply mem_cons
| (succ k) (a::l) := assume P, by
                  rewrite [kth_succ_of_cons]; apply mem_cons_of_mem a; apply kth_mem

-- Leo provided the following proof.
lemma eq_of_kth_eq [deceqA : decidable_eq A]
      : ∀ {l1 l2 : list A} (Pleq : length l1 = length l2),
          (∀ (k : nat) (Plt1 : k < length l1) (Plt2 : k < length l2), kth k l1 Plt1 = kth k l2 Plt2) → l1 = l2
| []       []       h₁ h₂ := rfl
| (a₁::l₁) []       h₁ h₂ := by contradiction
| []       (a₂::l₂) h₁ h₂ := by contradiction
| (a₁::l₁) (a₂::l₂) h₁ h₂ :=
  have ih₁ : length l₁ = length l₂, by injection h₁; eassumption,
  have ih₂ : ∀ (k : nat) (plt₁ : k < length l₁) (plt₂ : k < length l₂), kth k l₁ plt₁ = kth k l₂ plt₂,
    begin
      intro k plt₁ plt₂,
      have splt₁ : succ k < length l₁ + 1, from succ_le_succ plt₁,
      have splt₂ : succ k < length l₂ + 1, from succ_le_succ plt₂,
      have keq   : kth (succ k) (a₁::l₁) splt₁ = kth (succ k) (a₂::l₂) splt₂, from h₂ (succ k) splt₁ splt₂,
      rewrite *kth_succ_of_cons at keq,
      exact keq
    end,
  assert ih  : l₁ = l₂, from eq_of_kth_eq ih₁ ih₂,
  assert k₁  : a₁ = a₂,
    begin
      have lt₁ : 0 < length (a₁::l₁), from !zero_lt_succ,
      have lt₂ : 0 < length (a₂::l₂), from !zero_lt_succ,
      have e₁  : kth 0 (a₁::l₁) lt₁ = kth 0 (a₂::l₂) lt₂, from h₂ 0 lt₁ lt₂,
      rewrite *kth_zero_of_cons at e₁,
      assumption
    end,
  by subst l₁; subst a₁

lemma kth_of_map {B : Type} {f : A → B} :
      ∀ {k : nat} {l : list A} Plt Pmlt, kth k (map f l) Pmlt = f (kth k l Plt)
| k []            := assume P, absurd P !not_lt_zero
| 0 (a::l)        := assume Plt, by
                  rewrite [map_cons]; intro Pmlt; rewrite [kth_zero_of_cons]
| (succ k) (a::l) := assume P, begin
                  rewrite [map_cons], intro Pmlt, rewrite [*kth_succ_of_cons],
                  apply kth_of_map
                  end

lemma kth_find [deceqA : decidable_eq A] :
      ∀ {l : list A} {a} P, kth (find a l) l P = a
| []            := take a, assume P, absurd P !not_lt_zero
| (x::l)        := take a, begin
                assert Pd : decidable (a = x), {apply deceqA},
                cases Pd with Pe Pne,
                  rewrite [find_cons_of_eq l Pe], intro P, rewrite [kth_zero_of_cons, Pe],
                  rewrite [find_cons_of_ne l Pne], intro P, rewrite [kth_succ_of_cons],
                  apply kth_find
                end

lemma find_kth [deceqA : decidable_eq A] :
      ∀ {k : nat} {l : list A} P, find (kth k l P) l < length l
| k []            := assume P, absurd P !not_lt_zero
| 0 (a::l)        := assume P, begin
                  rewrite [kth_zero_of_cons, find_cons_of_eq l rfl, length_cons],
                  exact !zero_lt_succ
                  end
| (succ k) (a::l) := assume P, begin
                  rewrite [kth_succ_of_cons],
                  assert Pd : decidable ((kth k l (lt_of_succ_lt_succ P)) = a),
                    {apply deceqA},
                  cases Pd with Pe Pne,
                    rewrite [find_cons_of_eq l Pe], apply zero_lt_succ,
                    rewrite [find_cons_of_ne l Pne], apply succ_lt_succ, apply find_kth
                  end

lemma find_kth_of_nodup [deceqA : decidable_eq A] :
      ∀ {k : nat} {l : list A} P, nodup l → find (kth k l P) l = k
| k []            := assume P, absurd P !not_lt_zero
| 0 (a::l)        := assume Plt Pnodup,
                  by rewrite [kth_zero_of_cons, find_cons_of_eq l rfl]
| (succ k) (a::l) := assume Plt Pnodup, begin
                  rewrite [kth_succ_of_cons],
                  assert Pd : decidable ((kth k l (lt_of_succ_lt_succ Plt)) = a),
                    {apply deceqA},
                  cases Pd with Pe Pne,
                    assert Pin : a ∈ l, {rewrite -Pe, apply kth_mem},
                    exact absurd Pin (not_mem_of_nodup_cons Pnodup),
                    rewrite [find_cons_of_ne l Pne], apply congr (eq.refl succ),
                    apply find_kth_of_nodup (lt_of_succ_lt_succ Plt) (nodup_of_nodup_cons Pnodup)
                  end

end kth

end list


namespace fintype
open list

section found

variables {A B : Type}
variable [finA : fintype A]
include finA

lemma find_in_range [deceqB : decidable_eq B] {f : A → B} (b : B) :
    ∀ (l : list A) (P : find b (map f l) < length l), f (kth (find b (map f l)) l P) = b
| []       := assume P, begin exact absurd P !not_lt_zero end
| (a::l)   := decidable.rec_on (deceqB b (f a))
              (assume Peq, begin
              rewrite [map_cons f a l, find_cons_of_eq _ Peq],
              intro P, rewrite [kth_zero_of_cons], exact (Peq⁻¹)
              end)
              (assume Pne, begin
              rewrite [map_cons f a l, find_cons_of_ne _ Pne],
              intro P,
              rewrite [kth_succ_of_cons (find b (map f l)) l P],
              exact find_in_range l (lt_of_succ_lt_succ P)
              end)

end found

section list_to_fun
variables {A B : Type}
variable [finA : fintype A]
include finA

definition fun_to_list (f : A → B) : list B := map f (elems A)

lemma length_map_of_fintype (f : A → B) : length (map f (elems A)) = card A :=
      by apply length_map

variable [deceqA : decidable_eq A]
include deceqA

lemma fintype_find (a : A) : find a (elems A) < card A :=
      find_lt_length (complete a)

definition list_to_fun (l : list B) (leq : length l = card A) : A → B :=
           take x,
           kth _ _ (leq⁻¹ ▸ fintype_find x)

definition all_funs [finB : fintype B] : list (A → B) :=
           dmap (λ l, length l = card A) list_to_fun (all_lists_of_len (card A))

lemma list_to_fun_apply (l : list B) (leq : length l = card A) (a : A) :
      ∀ P, list_to_fun l leq a = kth (find a (elems A)) l P :=
      assume P, rfl

variable [deceqB : decidable_eq B]
include deceqB

lemma fun_eq_list_to_fun_map (f : A → B) : ∀ P, f = list_to_fun (map f (elems A)) P :=
      assume Pleq, funext (take a,
      assert Plt : _, from Pleq⁻¹ ▸ find_lt_length (complete a), begin
      rewrite [list_to_fun_apply _ Pleq a (Pleq⁻¹ ▸ find_lt_length (complete a))],
      assert Pmlt : find a (elems A) < length (map f (elems A)),
        {rewrite length_map, exact Plt},
      rewrite [@kth_of_map A B f (find a (elems A)) (elems A) Plt _, kth_find]
      end)

lemma list_eq_map_list_to_fun  (l : list B) (leq : length l = card A)
                    : l = map (list_to_fun l leq) (elems A) :=
      begin
      apply eq_of_kth_eq, rewrite length_map, apply leq,
        intro k Plt Plt2,
        assert Plt1 : k < length (elems A), {apply leq ▸ Plt},
        assert Plt3 : find (kth k (elems A) Plt1) (elems A) < length l,
          {rewrite leq, apply find_kth},
        rewrite [kth_of_map Plt1 Plt2, list_to_fun_apply l leq _ Plt3],
        congruence,
        rewrite [find_kth_of_nodup Plt1 (unique A)],
      end

lemma fun_to_list_to_fun (f : A → B) : ∀ P, list_to_fun (fun_to_list f) P = f :=
      assume P, (fun_eq_list_to_fun_map f P)⁻¹

lemma list_to_fun_to_list (l : list B) (leq : length l = card A) :
      fun_to_list (list_to_fun l leq) = l
      := (list_eq_map_list_to_fun l leq)⁻¹

lemma dinj_list_to_fun : dinj (λ (l : list B), length l = card A) list_to_fun :=
      take l1 l2 Pl1 Pl2 Peq,
      by rewrite [list_eq_map_list_to_fun l1 Pl1, list_eq_map_list_to_fun l2 Pl2, Peq]

variable [finB : fintype B]
include finB

lemma nodup_all_funs : nodup (@all_funs A B _ _ _) :=
      dmap_nodup_of_dinj dinj_list_to_fun (nodup_all_lists _)

lemma all_funs_complete (f : A → B) : f ∈ all_funs :=
      assert Plin : map f (elems A) ∈ all_lists_of_len (card A),
        from mem_all_lists (card A) _ (by rewrite length_map),
      assert Plfin : list_to_fun (map f (elems A)) (length_map_of_fintype f) ∈ all_funs,
        from mem_dmap _ Plin,
      begin rewrite [fun_eq_list_to_fun_map f (length_map_of_fintype f)], apply Plfin end

lemma all_funs_to_all_lists : map fun_to_list (@all_funs A B _ _ _) = all_lists_of_len (card A) :=
      map_dmap_of_pos_of_inv list_to_fun_to_list leq_of_mem_all_lists

lemma length_all_funs : length (@all_funs A B _ _ _) = (card B) ^ (card A) := calc
      length _ = length (map fun_to_list all_funs) : length_map
           ... = length (all_lists_of_len (card A)) : all_funs_to_all_lists
           ... = (card B) ^ (card A) : length_all_lists

definition fun_is_fintype [instance] : fintype (A → B) :=
           fintype.mk all_funs nodup_all_funs all_funs_complete

lemma card_funs : card (A → B) = (card B) ^ (card A) := length_all_funs

end list_to_fun

section surj_inv
variables {A B : Type}
variable [finA : fintype A]
include finA

-- surj from fintype domain implies fintype range
lemma mem_map_of_surj {f : A → B} (surj : surjective f) : ∀ b, b ∈ map f (elems A) :=
      take b, obtain a Peq, from surj b,
      Peq ▸ mem_map f (complete a)

variable [deceqB : decidable_eq B]
include deceqB

lemma found_of_surj {f : A → B} (surj : surjective f) :
      ∀ b, let elts := elems A, k := find b (map f elts) in k < length elts :=
      λ b, let elts := elems A, img := map f elts, k := find b img in
           have Pin : b ∈ img, from mem_map_of_surj surj b,
           assert Pfound : k < length img, from find_lt_length (mem_map_of_surj surj b),
           length_map f elts ▸ Pfound

definition right_inv {f : A → B} (surj : surjective f) : B → A :=
           λ b, let elts := elems A, k := find b (map f elts) in
           kth k elts (found_of_surj surj b)

lemma id_of_right_inv {f : A → B} (surj : surjective f) : f ∘ (right_inv surj) = id :=
      funext (λ b, find_in_range b (elems A) (found_of_surj surj b))
end surj_inv

-- inj functions for equal card types are also surj and therefore bij
-- the right inv (since it is surj) is also the left inv
section inj
variables {A B : Type}
variable [finA : fintype A]
include finA
variable [deceqA : decidable_eq A]
include deceqA
variable [finB : fintype B]
include finB
variable [deceqB : decidable_eq B]
include deceqB
open finset

lemma surj_of_inj_eq_card : card A = card B → ∀ {f : A → B}, injective f → surjective f :=
      assume Peqcard, take f, assume Pinj,
      decidable.rec_on decidable_forall_finite
      (assume P : surjective f, P)
      (assume Pnsurj : ¬surjective f, obtain b Pne, from exists_not_of_not_forall Pnsurj,
      assert Pall : ∀ a, f a ≠ b, from forall_not_of_not_exists Pne,
      assert Pbnin : b ∉ image f univ, from λ Pin,
        obtain a Pa, from exists_of_mem_image Pin, absurd (and.right Pa) (Pall a),
      assert Puniv : finset.card (image f univ) = card A,
        from card_eq_card_image_of_inj Pinj,
      assert Punivb : finset.card (image f univ) = card B, from eq.trans Puniv Peqcard,
      assert P : image f univ = univ, from univ_of_card_eq_univ Punivb,
      absurd (P⁻¹▸ mem_univ b) Pbnin)

end inj
end fintype
