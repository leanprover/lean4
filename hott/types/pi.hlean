/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn
Ported from Coq HoTT

Theorems about pi-types (dependent function spaces)
-/

import ..trunc ..axioms.funext .sigma
open path equiv is_equiv funext

namespace pi
  universe variables l k
  variables {A A' : Type.{l}} {B : A → Type.{k}} {C : Πa, B a → Type}
            {D : Πa b, C a b → Type}
            {a a' a'' : A} {b b₁ b₂ : B a} {b' : B a'} {b'' : B a''} {f g : Πa, B a}

  /- Paths -/

  /- Paths [p : f ≈ g] in a function type [Πx:X, P x] are equivalent to functions taking values in path types, [H : Πx:X, f x ≈ g x], or concisely, [H : f ∼ g].

  This equivalence, however, is just the combination of [apD10] and function extensionality [funext], and as such, [path_forall], et seq. are given in axioms.funext and path:  -/

  /- Now we show how these things compute. -/

  definition apD10_path_pi [H : funext] (h : f ∼ g) : apD10 (path_pi h) ∼ h :=
  apD10 (retr apD10 h)

  definition path_pi_eta [H : funext] (p : f ≈ g) : path_pi (apD10 p) ≈ p :=
  sect apD10 p

  definition path_pi_idp [H : funext] : path_pi (λx : A, idpath (f x)) ≈ idpath f :=
  !path_pi_eta

  /- The identification of the path space of a dependent function space, up to equivalence, is of course just funext. -/

  definition path_equiv_homotopy [H : funext] (f g : Πx, B x) : (f ≈ g) ≃ (f ∼ g) :=
  equiv.mk _ !funext.ap

  definition is_equiv_path_pi [instance] [H : funext] (f g : Πx, B x)
      : is_equiv (@path_pi _ _ _ f g) :=
  inv_closed apD10

  definition homotopy_equiv_path [H : funext] (f g : Πx, B x) : (f ∼ g) ≃ (f ≈ g) :=
  equiv.mk _ !is_equiv_path_pi


  /- Transport -/

  protected definition transport (p : a ≈ a') (f : Π(b : B a), C a b)
    : (transport (λa, Π(b : B a), C a b) p f)
      ∼ (λb, transport (C a') !transport_pV (transportD _ _ p _ (f (p⁻¹ ▹ b)))) :=
  path.rec_on p (λx, idp)

  /- A special case of [transport_pi] where the type [B] does not depend on [A],
      and so it is just a fixed type [B]. -/
  definition transport_constant {C : A → A' → Type} (p : a ≈ a') (f : Π(b : A'), C a b)
    : (path.transport (λa, Π(b : A'), C a b) p f) ∼ (λb, path.transport (λa, C a b) p (f b)) :=
  path.rec_on p (λx, idp)

  /- Maps on paths -/

  /- The action of maps given by lambda. -/
  definition ap_lambdaD [H : funext] {C : A' → Type} (p : a ≈ a') (f : Πa b, C b) :
    ap (λa b, f a b) p ≈ path_pi (λb, ap (λa, f a b) p) :=
  begin
    apply (path.rec_on p),
    apply inverse,
    apply path_pi_idp
  end

  /- Dependent paths -/

  /- with more implicit arguments the conclusion of the following theorem is
     (Π(b : B a), transportD B C p b (f b) ≈ g (path.transport B p b)) ≃
     (path.transport (λa, Π(b : B a), C a b) p f ≈ g) -/
  definition dpath_pi [H : funext] (p : a ≈ a') (f : Π(b : B a), C a b) (g : Π(b' : B a'), C a' b')
    : (Π(b : B a), p ▹D (f b) ≈ g (p ▹ b)) ≃ (p ▹ f ≈ g) :=
  path.rec_on p (λg, !homotopy_equiv_path) g

  section open sigma.ops
  /- more implicit arguments:
  (Π(b : B a), path.transport C (sigma.path p idp) (f b) ≈ g (p ▹ b)) ≃
  (Π(b : B a), transportD B (λ(a : A) (b : B a), C ⟨a, b⟩) p b (f b) ≈ g (path.transport B p b)) -/
  definition dpath_pi_sigma {C : (Σa, B a) → Type} (p : a ≈ a')
    (f : Π(b : B a), C ⟨a, b⟩) (g : Π(b' : B a'), C ⟨a', b'⟩) :
    (Π(b : B a), (sigma.path p idp) ▹ (f b) ≈ g (p ▹ b)) ≃ (Π(b : B a), p ▹D (f b) ≈ g (p ▹ b)) :=
  path.rec_on p (λg, !equiv.refl) g
  end

  /- truncation -/

  open truncation
  definition trunc_pi [instance] [H : funext.{l k}] (B : A → Type.{k}) (n : trunc_index)
      [H : ∀a, is_trunc n (B a)] : is_trunc n (Πa, B a) :=
  begin
    reverts (B, H),
    apply (trunc_index.rec_on n),
      intros (B, H),
        fapply is_contr.mk,
          intro a, apply center, apply H, --remove "apply H" when term synthesis works correctly
          intro f, apply path_pi,
            intro x, apply (contr (f x)),
      intros (n, IH, B, H),
        fapply is_trunc_succ, intros (f, g),
          fapply trunc_equiv',
            apply equiv.symm, apply path_equiv_homotopy,
            apply IH,
              intro a,
              show is_trunc n (f a ≈ g a), from
              succ_is_trunc n (f a) (g a)
  end

  definition trunc_path_pi [instance] [H : funext.{l k}] (n : trunc_index) (f g : Πa, B a)
      [H : ∀a, is_trunc n (f a ≈ g a)] : is_trunc n (f ≈ g) :=
  begin
    apply trunc_equiv', apply equiv.symm,
    apply path_equiv_homotopy,
    apply trunc_pi, exact H,
  end

end pi
