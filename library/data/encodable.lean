/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

Type class for encodable types.
Note that every encodable type is countable.
-/
import data.fintype data.list data.sum data.nat data.subtype data.countable data.equiv
open option list nat function

structure encodable [class] (A : Type) :=
(encode : A → nat) (decode : nat → option A) (encodek : ∀ a, decode (encode a) = some a)

open encodable

definition countable_of_encodable {A : Type} : encodable A → countable A :=
assume e : encodable A,
have injective encode, from
  λ (a₁ a₂ : A) (h : encode a₁ = encode a₂),
    assert decode A (encode a₁) = decode A (encode a₂), by rewrite h,
    by rewrite [*encodek at this]; injection this; assumption,
exists.intro encode this

definition encodable_fintype [instance] {A : Type} [h₁ : fintype A] [h₂ : decidable_eq A] : encodable A :=
encodable.mk
  (λ a, find a (elements_of A))
  (λ n, nth (elements_of A) n)
  (λ a, find_nth (fintype.complete a))

definition encodable_nat [instance] : encodable nat :=
encodable.mk (λ a, a) (λ n, some n) (λ a, rfl)

definition encodable_option [instance] {A : Type} [h : encodable A] : encodable (option A) :=
encodable.mk
  (λ o, match o with
        | some a := succ (encode a)
        | none := 0
        end)
  (λ n, if n = 0 then some none else some (decode A (pred n)))
  (λ o,
    begin
    cases o with a,
      begin esimp end,
      begin esimp, rewrite [if_neg !succ_ne_zero, encodable.encodek] end
    end)

section sum
variables {A B : Type}
variables [h₁ : encodable A] [h₂ : encodable B]
include h₁ h₂

definition encode_sum : sum A B → nat
| (sum.inl a) := 2 * encode a
| (sum.inr b) := 2 * encode b + 1

definition decode_sum (n : nat) : option (sum A B) :=
if n mod 2 = 0 then
   match decode A (n div 2) with
   | some a := some (sum.inl a)
   | none   := none
   end
else
   match decode B ((n - 1) div 2) with
   | some b := some (sum.inr b)
   | none   := none
   end

open decidable
theorem decode_encode_sum : ∀ s : sum A B, decode_sum (encode_sum s) = some s
| (sum.inl a) :=
  assert aux : 2 > 0, from dec_trivial,
  begin
    esimp [encode_sum, decode_sum],
    rewrite [mul_mod_right, if_pos (eq.refl 0), mul_div_cancel_left _ aux, encodable.encodek]
  end
| (sum.inr b) :=
  assert aux₁ : 2 > 0,       from dec_trivial,
  assert aux₂ : 1 mod 2 = 1, by rewrite [nat.modulo_def],
  assert aux₃ : 1 ≠ 0,       from dec_trivial,
  begin
    esimp [encode_sum, decode_sum],
    rewrite [add.comm, add_mul_mod_self_left, aux₂, if_neg aux₃, add_sub_cancel_left,
             mul_div_cancel_left _ aux₁, encodable.encodek]
  end

definition encodable_sum [instance] : encodable (sum A B) :=
encodable.mk
  (λ s, encode_sum s)
  (λ n, decode_sum n)
  (λ s, decode_encode_sum s)
end sum

section prod
variables {A B : Type}
variables [h₁ : encodable A] [h₂ : encodable B]
include h₁ h₂

definition encode_prod : A × B → nat
| (a, b) := mkpair (encode a) (encode b)

definition decode_prod (n : nat) : option (A × B) :=
match unpair n with
| (n₁, n₂) :=
  match decode A n₁ with
  | some a :=
    match decode B n₂ with
    | some b := some (a, b)
    | none   := none
    end
  | none   := none
  end
end

theorem decode_encode_prod : ∀ p : A × B, decode_prod (encode_prod p) = some p
| (a, b) :=
  begin
    esimp [encode_prod, decode_prod, prod.cases_on],
    rewrite [unpair_mkpair],
    esimp,
    rewrite [*encodable.encodek]
  end

definition encodable_product [instance] : encodable (A × B) :=
encodable.mk
  encode_prod
  decode_prod
  decode_encode_prod
end prod

section list
variables {A : Type}
variables [h : encodable A]
include h

definition encode_list_core : list A → nat
| []     := 0
| (a::l) := mkpair (encode a) (encode_list_core l)

theorem encode_list_core_cons (a : A) (l : list A) : encode_list_core (a::l) = mkpair (encode a) (encode_list_core l) :=
rfl

definition encode_list (l : list A) : nat :=
mkpair (length l) (encode_list_core l)

definition decode_list_core : nat → nat → option (list A)
| 0        v  := some []
| (succ n) v  :=
  match unpair v with
  | (v₁, v₂) :=
    match decode A v₁ with
    | some a :=
      match decode_list_core n v₂ with
      | some l := some (a::l)
      | none   := none
      end
    | none   := none
    end
  end

theorem decode_list_core_succ (n v : nat) :
  decode_list_core (succ n) v =
    match unpair v with
    | (v₁, v₂) :=
      match decode A v₁ with
      | some a :=
        match decode_list_core n v₂ with
        | some l := some (a::l)
        | none   := none
        end
      | none   := none
      end
    end
:= rfl

definition decode_list (n : nat) : option (list A) :=
match unpair n with
| (l, v) := decode_list_core l v
end

theorem decode_encode_list_core : ∀ l : list A, decode_list_core (length l) (encode_list_core l) = some l
| []     := rfl
| (a::l) :=
  begin
    rewrite [encode_list_core_cons, length_cons, add_one (length l), decode_list_core_succ],
    rewrite [unpair_mkpair],
    esimp [prod.cases_on],
    rewrite [decode_encode_list_core l],
    rewrite [encodable.encodek],
  end

theorem decode_encode_list (l : list A) : decode_list (encode_list l) = some l :=
begin
  esimp [encode_list, decode_list],
  rewrite [unpair_mkpair],
  esimp [prod.cases_on],
  apply decode_encode_list_core
end

definition encodable_list [instance] : encodable (list A) :=
encodable.mk
  encode_list
  decode_list
  decode_encode_list
end list

definition encodable_of_left_injection
             {A B : Type} [h₁ : encodable A]
             (f : B → A) (finv : A → option B) (linv : ∀ b, finv (f b) = some b) : encodable B :=
encodable.mk
  (λ b, encode (f b))
  (λ n,
    match decode A n with
    | some a := finv a
    | none   := none
    end)
  (λ b,
    begin
      esimp,
      rewrite [encodable.encodek],
      esimp [option.cases_on],
      rewrite [linv]
    end)

section
open equiv

definition encodable_of_equiv {A B : Type} [h : encodable A] : A ≃ B → encodable B
| (mk f g l r) :=
  encodable_of_left_injection g (λ a, some (f a))
    (λ b, by rewrite r; reflexivity)
end

/-
Choice function for encodable types  and decidable predicates.
We provide the following API

choose      {A : Type} {p : A → Prop} [c : encodable A] [d : decidable_pred p] : (∃ x, p x) → A :=
choose_spec {A : Type} {p : A → Prop} [c : encodable A] [d : decidable_pred p] (ex : ∃ x, p x) : p (choose ex) :=
-/
section find_a
parameters {A : Type} {p : A → Prop} [c : encodable A] [d : decidable_pred p]
include c
include d

private definition pn (n : nat) : Prop :=
match decode A n with
| some a := p a
| none   := false
end

private definition decidable_pn : decidable_pred pn :=
λ n,
match decode A n with
| some a := λ e : decode A n = some a,
  match d a with
  | decidable.inl t :=
    begin
      unfold pn, rewrite e, esimp [option.cases_on],
      exact (decidable.inl t)
    end
  | decidable.inr f :=
    begin
      unfold pn, rewrite e, esimp [option.cases_on],
      exact (decidable.inr f)
    end
  end
| none   := λ e : decode A n = none,
  begin
    unfold pn, rewrite e, esimp [option.cases_on],
    exact decidable_false
  end
end (eq.refl (decode A n))

private definition ex_pn_of_ex : (∃ x, p x) → (∃ x, pn x) :=
assume ex,
obtain (w : A) (pw : p w), from ex,
exists.intro (encode w)
  begin
    unfold pn, rewrite [encodek], esimp, exact pw
  end

private lemma decode_ne_none_of_pn {n : nat} : pn n → decode A n ≠ none :=
assume pnn e,
begin
  rewrite [▸ (match decode A n with | some a := p a | none   := false end) at pnn],
  rewrite [e at pnn], esimp [option.cases_on] at pnn,
  exact (false.elim pnn)
end

open subtype

private definition of_nat (n : nat) : pn n → { a : A | p a } :=
match decode A n with
| some a := λ (e : decode A n = some a),
  begin
    unfold pn, rewrite e, esimp [option.cases_on], intro pa,
    exact (tag a pa)
  end
| none   := λ (e : decode A n = none) h, absurd e (decode_ne_none_of_pn h)
end (eq.refl (decode A n))

private definition find_a : (∃ x, p x) → {a : A | p a} :=
suppose ∃ x, p x,
have    ∃ x, pn x, from ex_pn_of_ex this,
let r := @nat.find _ decidable_pn this in
have pn r, from @nat.find_spec pn decidable_pn this,
of_nat r this
end find_a

namespace encodable
open subtype

definition choose {A : Type} {p : A → Prop} [c : encodable A] [d : decidable_pred p] : (∃ x, p x) → A :=
assume ex, elt_of (find_a ex)

theorem choose_spec {A : Type} {p : A → Prop} [c : encodable A] [d : decidable_pred p] (ex : ∃ x, p x) : p (choose ex) :=
has_property (find_a ex)

theorem axiom_of_choice {A : Type} {B : A → Type} {R : Π x, B x → Prop} [c : Π a, encodable (B a)] [d : ∀ x y, decidable (R x y)]
                        : (∀x, ∃y, R x y) → ∃f, ∀x, R x (f x) :=
assume H,
have ∀x, R x (choose (H x)), from take x, choose_spec (H x),
exists.intro _ this

theorem skolem {A : Type} {B : A → Type} {P : Π x, B x → Prop} [c : Π a, encodable (B a)] [d : ∀ x y, decidable (P x y)]
               : (∀x, ∃y, P x y) ↔ ∃f, (∀x, P x (f x)) :=
iff.intro
  (suppose (∀ x, ∃y, P x y), axiom_of_choice this)
  (suppose (∃ f, (∀x, P x (f x))),
   take x, obtain (fw : ∀x, B x) (Hw : ∀x, P x (fw x)), from this,
     exists.intro (fw x) (Hw x))
end encodable

namespace quot
section
open setoid encodable
parameter {A : Type}
parameter {s : setoid A}
parameter [decR : ∀ a b : A, decidable (a ≈ b)]
parameter [encA : encodable A]
include decR
include encA

-- Choose equivalence class representative
definition rep (q : quot s) : A :=
choose (exists_rep q)

theorem rep_spec (q : quot s) : ⟦rep q⟧ = q :=
choose_spec (exists_rep q)
end
end quot
