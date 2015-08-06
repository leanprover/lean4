/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn
Ported from Coq HoTT

Theorems about pi-types (dependent function spaces)
-/
import types.sigma

open eq equiv is_equiv funext

namespace pi
  universe variables l k
  variables {A A' : Type.{l}} {B : A → Type.{k}} {B' : A' → Type.{k}} {C : Πa, B a → Type}
            {D : Πa b, C a b → Type}
            {a a' a'' : A} {b b₁ b₂ : B a} {b' : B a'} {b'' : B a''} {f g : Πa, B a}

  /- Paths -/

  /- Paths [p : f ≈ g] in a function type [Πx:X, P x] are equivalent to functions taking values in path types, [H : Πx:X, f x ≈ g x], or concisely, [H : f ∼ g].

  This equivalence, however, is just the combination of [apD10] and function extensionality [funext], and as such, [path_forall], et seq. are given in axioms.funext and path:  -/

  /- Now we show how these things compute. -/

  definition apd10_path_pi (H : funext) (h : f ~ g) : apd10 (eq_of_homotopy h) ~ h :=
  apd10 (right_inv apd10 h)

  definition path_pi_eta (H : funext) (p : f = g) : eq_of_homotopy (apd10 p) = p :=
  left_inv apd10 p

  print classes

  definition path_pi_idp (H : funext) : eq_of_homotopy (λx : A, refl (f x)) = refl f :=
  path_pi_eta H _

  /- The identification of the path space of a dependent function space, up to equivalence, is of course just funext. -/

  definition path_equiv_homotopy (H : funext) (f g : Πx, B x) : (f = g) ≃ (f ~ g) :=
  equiv.mk _ !is_equiv_apd

  definition is_equiv_path_pi [instance] (H : funext) (f g : Πx, B x)
      : is_equiv (@eq_of_homotopy _ _ f g) :=
  is_equiv_inv apd10

  definition homotopy_equiv_path (H : funext) (f g : Πx, B x) : (f ~ g) ≃ (f = g) :=
  equiv.mk _ (is_equiv_path_pi H f g)

  /- Transport -/

  protected definition transport (p : a = a') (f : Π(b : B a), C a b)
    : (transport (λa, Π(b : B a), C a b) p f)
      ~ (λb, transport (C a') !tr_inv_tr (transportD _ p _ (f (p⁻¹ ▸ b)))) :=
  eq.rec_on p (λx, idp)

  /- A special case of [transport_pi] where the type [B] does not depend on [A],
      and so it is just a fixed type [B]. -/
  definition transport_constant {C : A → A' → Type} (p : a = a') (f : Π(b : A'), C a b)
    : (eq.transport (λa, Π(b : A'), C a b) p f) ~ (λb, eq.transport (λa, C a b) p (f b)) :=
  eq.rec_on p (λx, idp)

  /- Maps on paths -/

  /- The action of maps given by lambda. -/
  definition ap_lambdaD (H : funext) {C : A' → Type} (p : a = a') (f : Πa b, C b) :
    ap (λa b, f a b) p = eq_of_homotopy (λb, ap (λa, f a b) p) :=
  begin
    apply (eq.rec_on p),
    apply inverse,
    apply (path_pi_idp H)
  end

  /- Dependent paths -/

  /- with more implicit arguments the conclusion of the following theorem is
     (Π(b : B a), transportD B C p b (f b) = g (eq.transport B p b)) ≃
     (eq.transport (λa, Π(b : B a), C a b) p f = g) -/
  definition dpath_pi (H : funext) (p : a = a') (f : Π(b : B a), C a b) (g : Π(b' : B a'), C a' b')
    : (Π(b : B a), p ▸D (f b) = g (p ▸ b)) ≃ (p ▸ f = g) :=
  eq.rec_on p (λg, homotopy_equiv_path H f g) g

  section open sigma sigma.ops
  /- more implicit arguments:
  (Π(b : B a), eq.transport C (sigma.path p idp) (f b) = g (p ▸ b)) ≃
  (Π(b : B a), transportD B (λ(a : A) (b : B a), C ⟨a, b⟩) p b (f b) = g (eq.transport B p b)) -/
  definition dpath_pi_sigma {C : (Σa, B a) → Type} (p : a = a')
    (f : Π(b : B a), C ⟨a, b⟩) (g : Π(b' : B a'), C ⟨a', b'⟩) :
    (Π(b : B a), (sigma.sigma_eq p !pathover_tr) ▸ (f b) = g (p ▸ b)) ≃ (Π(b : B a), p ▸D (f b) = g (p ▸ b)) :=
  eq.rec_on p (λg, !equiv.refl) g
  end

  variables (f0 : A' → A) (f1 : Π(a':A'), B (f0 a') → B' a')

  definition transport_V [reducible] (P : A → Type) {x y : A} (p : x = y) (u : P y) : P x :=
  p⁻¹ ▸ u

  definition functor_pi : (Π(a:A), B a) → (Π(a':A'), B' a') := (λg a', f1 a' (g (f0 a')))
  /- Equivalences -/
  definition isequiv_functor_pi [instance] (f0 : A' → A) (f1 : Π(a':A'), B (f0 a') → B' a')
    [H0 : is_equiv f0] [H1 : Πa', @is_equiv (B (f0 a')) (B' a') (f1 a')]
      : is_equiv (functor_pi f0 f1) :=
  begin
  apply (adjointify (functor_pi f0 f1) (functor_pi (f0⁻¹)
        (λ(a : A) (b' : B' (f0⁻¹ a)), transport B (right_inv f0 a) ((f1 (f0⁻¹ a))⁻¹ b')))),
  intro h, apply eq_of_homotopy,
  esimp [functor_pi, function.compose], -- simplify (and unfold function_pi and function.compose)
  --first subgoal
  intro a', esimp,
  rewrite adj,
  rewrite -tr_compose,
  rewrite {f1 a' _}(fn_tr_eq_tr_fn _ f1 _),
  rewrite (right_inv (f1 _) _),
  apply apd,
  intro h,
  apply eq_of_homotopy, intro a, esimp,
  apply (transport_V (λx, right_inv f0 a ▸ x = h a) (left_inv (f1 _) _)),
  apply apd
  end

end pi
