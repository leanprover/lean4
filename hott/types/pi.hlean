/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: types.pi
Author: Floris van Doorn

Ported from Coq HoTT
Theorems about pi-types (dependent function spaces)
-/

import types.sigma

open eq equiv is_equiv funext

namespace pi
  variables {A A' : Type} {B : A → Type} {B' : A' → Type} {C : Πa, B a → Type}
            {D : Πa b, C a b → Type}
            {a a' a'' : A} {b b₁ b₂ : B a} {b' : B a'} {b'' : B a''} {f g : Πa, B a}

  /- Paths -/

  /- Paths [p : f ≈ g] in a function type [Πx:X, P x] are equivalent to functions taking values in path types, [H : Πx:X, f x ≈ g x], or concisely, [H : f ∼ g].

  This equivalence, however, is just the combination of [apd10] and function extensionality [funext], and as such, [path_forall], et seq. are given in axioms.funext and path:  -/

  /- Now we show how these things compute. -/

  definition apd10_eq_of_homotopy (h : f ∼ g) : apd10 (eq_of_homotopy h) ∼ h :=
  apd10 (right_inv apd10 h)

  definition eq_of_homotopy_eta (p : f = g) : eq_of_homotopy (apd10 p) = p :=
  left_inv apd10 p

  definition eq_of_homotopy_idp (f : Πa, B a) : eq_of_homotopy (λx : A, refl (f x)) = refl f :=
  !eq_of_homotopy_eta

  /- The identification of the path space of a dependent function space, up to equivalence, is of course just funext. -/

  definition eq_equiv_homotopy (f g : Πx, B x) : (f = g) ≃ (f ∼ g) :=
  equiv.mk _ !is_equiv_apd

  definition is_equiv_eq_of_homotopy [instance] (f g : Πx, B x)
      : is_equiv (@eq_of_homotopy _ _ f g) :=
  is_equiv_inv apd10

  definition homotopy_equiv_eq (f g : Πx, B x) : (f ∼ g) ≃ (f = g) :=
  equiv.mk _ !is_equiv_eq_of_homotopy


  /- Transport -/

  definition pi_transport (p : a = a') (f : Π(b : B a), C a b)
    : (transport (λa, Π(b : B a), C a b) p f)
      ∼ (λb, transport (C a') !tr_inv_tr (transportD _ p _ (f (p⁻¹ ▹ b)))) :=
  eq.rec_on p (λx, idp)

  /- A special case of [transport_pi] where the type [B] does not depend on [A],
      and so it is just a fixed type [B]. -/
  definition pi_transport_constant {C : A → A' → Type} (p : a = a') (f : Π(b : A'), C a b) (b : A')
    : (transport (λa, Π(b : A'), C a b) p f) b = transport (λa, C a b) p (f b) :=
  eq.rec_on p idp

  /- Maps on paths -/

  /- The action of maps given by lambda. -/
  definition ap_lambdaD {C : A' → Type} (p : a = a') (f : Πa b, C b) :
    ap (λa b, f a b) p = eq_of_homotopy (λb, ap (λa, f a b) p) :=
  begin
    apply (eq.rec_on p),
    apply inverse,
    apply eq_of_homotopy_idp
  end

  /- Dependent paths -/

  /- with more implicit arguments the conclusion of the following theorem is
     (Π(b : B a), transportD B C p b (f b) = g (transport B p b)) ≃
     (transport (λa, Π(b : B a), C a b) p f = g) -/
  definition heq_piD (p : a = a') (f : Π(b : B a), C a b)
    (g : Π(b' : B a'), C a' b') : (Π(b : B a), p ▹D (f b) = g (p ▹ b)) ≃ (p ▹ f = g) :=
  eq.rec_on p (λg, !homotopy_equiv_eq) g

  definition heq_pi {C : A → Type} (p : a = a') (f : Π(b : B a), C a)
    (g : Π(b' : B a'), C a') : (Π(b : B a), p ▹ (f b) = g (p ▹ b)) ≃ (p ▹ f = g) :=
  eq.rec_on p (λg, !homotopy_equiv_eq) g


  section
  open sigma sigma.ops
  /- more implicit arguments:
  (Π(b : B a), transport C (sigma_eq p idp) (f b) = g (p ▹ b)) ≃
  (Π(b : B a), transportD B (λ(a : A) (b : B a), C ⟨a, b⟩) p b (f b) = g (transport B p b)) -/
  definition heq_pi_sigma {C : (Σa, B a) → Type} (p : a = a')
    (f : Π(b : B a), C ⟨a, b⟩) (g : Π(b' : B a'), C ⟨a', b'⟩) :
    (Π(b : B a), (sigma_eq p idp) ▹ (f b) = g (p ▹ b)) ≃ (Π(b : B a), p ▹D (f b) = g (p ▹ b)) :=
  eq.rec_on p (λg, !equiv.refl) g
  end

  /- Functorial action -/
  variables (f0 : A' → A) (f1 : Π(a':A'), B (f0 a') → B' a')

  /- The functoriality of [forall] is slightly subtle: it is contravariant in the domain type and covariant in the codomain, but the codomain is dependent on the domain. -/

  definition pi_functor : (Π(a:A), B a) → (Π(a':A'), B' a') := (λg a', f1 a' (g (f0 a')))

  definition ap_pi_functor {g g' : Π(a:A), B a} (h : g ∼ g')
      : ap (pi_functor f0 f1) (eq_of_homotopy h) = eq_of_homotopy (λa':A', (ap (f1 a') (h (f0 a')))) :=
  begin
  apply (equiv_rect (@apd10 A B g g')), intro p, clear h,
  cases p,
  apply concat,
    exact (ap (ap (pi_functor f0 f1)) (eq_of_homotopy_idp g)),
    apply symm, apply eq_of_homotopy_idp
  end

  /- Equivalences -/

  definition is_equiv_pi_functor [instance]
    [H0 : is_equiv f0] [H1 : Πa', @is_equiv (B (f0 a')) (B' a') (f1 a')]
      : is_equiv (pi_functor f0 f1) :=
  begin
    apply (adjointify (pi_functor f0 f1) (pi_functor f0⁻¹
          (λ(a : A) (b' : B' (f0⁻¹ a)), transport B (right_inv f0 a) ((f1 (f0⁻¹ a))⁻¹ b')))),
    intro h, apply eq_of_homotopy,
    unfold pi_functor, unfold function.compose, unfold function.id,
    begin
      intro a',
      apply (tr_inv _ (adj f0 a')),
      apply (transport (λx, f1 a' x = h a') (transport_compose B f0 (left_inv f0 a') _)),
      apply (tr_inv (λx, x = h a') (fn_tr_eq_tr_fn _ f1 _)), unfold function.compose,
      apply (tr_inv (λx, left_inv f0 a' ▹ x = h a') (right_inv (f1 _) _)), unfold function.id,
      apply apd
    end,
    begin
      intro h,
      apply eq_of_homotopy, intro a,
      apply (tr_inv (λx, right_inv f0 a ▹ x = h a) (left_inv (f1 _) _)), unfold function.id,
      apply apd
    end
  end

  definition pi_equiv_pi_of_is_equiv [H : is_equiv f0] [H1 : Πa', @is_equiv (B (f0 a')) (B' a') (f1 a')]
    : (Πa, B a) ≃ (Πa', B' a') :=
  equiv.mk (pi_functor f0 f1) _

  definition pi_equiv_pi (f0 : A' ≃ A) (f1 : Πa', (B (to_fun f0 a') ≃ B' a'))
    : (Πa, B a) ≃ (Πa', B' a') :=
  pi_equiv_pi_of_is_equiv (to_fun f0) (λa', to_fun (f1 a'))

  definition pi_equiv_pi_id {P Q : A → Type} (g : Πa, P a ≃ Q a) : (Πa, P a) ≃ (Πa, Q a) :=
  pi_equiv_pi equiv.refl g

  /- Truncatedness: any dependent product of n-types is an n-type -/

  open is_trunc
  definition is_trunc_pi (B : A → Type) (n : trunc_index)
      [H : ∀a, is_trunc n (B a)] : is_trunc n (Πa, B a) :=
  begin
    reverts [B, H],
    apply (trunc_index.rec_on n),
      {intros [B, H],
        fapply is_contr.mk,
          intro a, apply center,
          intro f, apply eq_of_homotopy,
            intro x, apply (contr (f x))},
      {intros [n, IH, B, H],
        fapply is_trunc_succ_intro, intros [f, g],
          fapply is_trunc_equiv_closed,
            apply equiv.symm, apply eq_equiv_homotopy,
            apply IH,
              intro a,
              show is_trunc n (f a = g a), from
              is_trunc_eq n (f a) (g a)}
  end
  local attribute is_trunc_pi [instance]
  definition is_trunc_eq_pi [instance] [priority 500] (n : trunc_index) (f g : Πa, B a)
      [H : ∀a, is_trunc n (f a = g a)] : is_trunc n (f = g) :=
  begin
    apply is_trunc_equiv_closed, apply equiv.symm,
    apply eq_equiv_homotopy
  end

  /- Symmetry of Π -/

  definition is_equiv_flip [instance] {P : A → A' → Type} : is_equiv (@function.flip _ _ P) :=
  begin
    fapply is_equiv.mk,
    exact (@function.flip _ _ (function.flip P)),
    repeat (intro f; apply idp)
  end

  definition pi_comm_equiv {P : A → A' → Type} : (Πa b, P a b) ≃ (Πb a, P a b) :=
  equiv.mk (@function.flip _ _ P) _

end pi

attribute pi.is_trunc_pi [instance] [priority 1510]
