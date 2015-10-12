/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

Type class for encodable types.
Note that every encodable type is countable.
-/
import data.fintype data.list data.list.sort data.sum data.nat.div data.countable data.equiv data.finset
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
  assert aux : 2 > (0:nat), from dec_trivial,
  begin
    esimp [encode_sum, decode_sum],
    rewrite [mul_mod_right, if_pos (eq.refl (0 : nat)), mul_div_cancel_left _ aux, encodable.encodek]
  end
| (sum.inr b) :=
  assert aux₁ : 2 > (0:nat),       from dec_trivial,
  assert aux₂ : 1 mod 2 = (1:nat), by rewrite [nat.modulo_def],
  assert aux₃ : 1 ≠ (0:nat),       from dec_trivial,
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

section finset
variable {A : Type}
variable [encA : encodable A]
include encA

private definition enle (a b : A) : Prop := encode a ≤ encode b

private lemma enle.refl (a : A) : enle a a :=
!le.refl

private lemma enle.trans (a b c : A) : enle a b → enle b c → enle a c :=
assume h₁ h₂, le.trans h₁ h₂

private lemma enle.total (a b : A) : enle a b ∨ enle b a :=
le.total

private lemma enle.antisymm (a b : A) : enle a b → enle b a → a = b :=
assume h₁ h₂,
assert encode a = encode b, from le.antisymm h₁ h₂,
assert decode A (encode a) = decode A (encode b), by rewrite this,
assert some a = some b, by rewrite [*encodek at this]; exact this,
option.no_confusion this (λ e, e)

private definition decidable_enle [instance] (a b : A) : decidable (enle a b) :=
decidable_le (encode a) (encode b)

variables [decA : decidable_eq A]
include decA

private definition ensort (l : list A) : list A :=
sort enle l

open subtype perm
private lemma sorted_eq_of_perm {l₁ l₂ : list A} (h : l₁ ~ l₂) : ensort l₁ = ensort l₂ :=
list.sort_eq_of_perm_core enle.total enle.trans enle.refl enle.antisymm h

definition encode_finset (s : finset A) : nat :=
quot.lift_on s
  (λ l, encode (ensort (elt_of l)))
  (λ l₁ l₂ p,
    have elt_of l₁ ~ elt_of l₂,                     from p,
    assert ensort (elt_of l₁) = ensort (elt_of l₂), from sorted_eq_of_perm this,
    by rewrite this)

definition decode_finset (n : nat) : option (finset A) :=
match decode (list A) n with
| some l₁ := some (finset.to_finset l₁)
| none    := none
end

theorem decode_encode_finset (s : finset A) : decode_finset (encode_finset s) = some s :=
quot.induction_on s (λ l,
  begin
    unfold encode_finset, unfold decode_finset, rewrite encodek, esimp, congruence,
    apply quot.sound, cases l with l nd,
    show erase_dup (ensort l) ~ l, from
      have nodup (ensort l), from nodup_of_perm_of_nodup (perm.symm !sort_perm) nd,
      calc erase_dup (ensort l) = ensort l : erase_dup_eq_of_nodup this
                ...             ~ l        : sort_perm
  end)

definition encodable_finset [instance] : encodable (finset A) :=
encodable.mk
  encode_finset
  decode_finset
  decode_encode_finset
end finset

section subtype
open subtype decidable
variable {A : Type}
variable {P : A → Prop}
variable [encA : encodable A]
variable [decP : decidable_pred P]

include encA
definition encode_subtype : {a : A | P a} → nat
| (tag v h) := encode v

include decP
definition decode_subtype (v : nat) : option {a : A | P a} :=
match decode A v with
| some a := if h : P a then some (tag a h) else none
| none   := none
end

lemma decode_encode_subtype : ∀ s : {a : A | P a}, decode_subtype (encode_subtype s) = some s
| (tag v h) :=
  begin
    unfold [encode_subtype, decode_subtype], rewrite encodek, esimp,
    rewrite [dif_pos h]
  end

definition encodable_subtype [instance] : encodable {a : A | P a} :=
encodable.mk
  encode_subtype
  decode_subtype
  decode_encode_subtype
end subtype

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

definition encode_quot (q : quot s) : nat :=
encode (rep q)

definition decode_quot (n : nat) : option (quot s) :=
match decode A n with
| some a := some ⟦ a ⟧
| none   := none
end

lemma decode_encode_quot (q : quot s) : decode_quot (encode_quot q) = some q :=
quot.induction_on q (λ l, begin unfold [encode_quot, decode_quot], rewrite encodek, esimp, rewrite rep_spec end)

definition encodable_quot : encodable (quot s) :=
encodable.mk
  encode_quot
  decode_quot
  decode_encode_quot
end
end quot
attribute quot.encodable_quot [instance]
