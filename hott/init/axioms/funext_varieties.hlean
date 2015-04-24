/-
Copyright (c) 2014 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: init.axioms.funext_varieties
Authors: Jakob von Raumer

Ported from Coq HoTT
-/

prelude
import ..path ..trunc ..equiv

open eq is_trunc sigma function

/- In init.axioms.funext, we defined function extensionality to be the assertion
   that the map apd10 is an equivalence.   We now prove that this follows
   from a couple of weaker-looking forms of function extensionality.  We do
   require eta conversion, which Coq 8.4+ has judgmentally.

   This proof is originally due to Voevodsky; it has since been simplified
   by Peter Lumsdaine and Michael Shulman. -/

definition funext.{l k} :=
  Π ⦃A : Type.{l}⦄ {P : A → Type.{k}} (f g : Π x, P x), is_equiv (@apd10 A P f g)

-- Naive funext is the simple assertion that pointwise equal functions are equal.
-- TODO think about universe levels
definition naive_funext :=
  Π ⦃A : Type⦄ {P : A → Type} (f g : Πx, P x), (f ∼ g) → f = g

-- Weak funext says that a product of contractible types is contractible.
definition weak_funext :=
  Π ⦃A : Type⦄ (P : A → Type) [H: Πx, is_contr (P x)], is_contr (Πx, P x)

definition weak_funext_of_naive_funext : naive_funext → weak_funext :=
  (λ nf A P (Pc : Πx, is_contr (P x)),
    let c := λx, center (P x) in
    is_contr.mk c (λ f,
      have eq' : (λx, center (P x)) ∼ f,
        from (λx, contr (f x)),
      have eq : (λx, center (P x)) = f,
        from nf A P (λx, center (P x)) f eq',
      eq
    )
  )

/- The less obvious direction is that WeakFunext implies Funext
  (and hence all three are logically equivalent).  The point is that under weak
  funext, the space of "pointwise homotopies" has the same universal property as
  the space of paths. -/

section
  universe variables l k
  parameters [wf : weak_funext.{l k}] {A : Type.{l}} {B : A → Type.{k}} (f : Π x, B x)

  definition is_contr_sigma_homotopy [instance] : is_contr (Σ (g : Π x, B x), f ∼ g) :=
    is_contr.mk (sigma.mk f (homotopy.refl f))
      (λ dp, sigma.rec_on dp
        (λ (g : Π x, B x) (h : f ∼ g),
          let r := λ (k : Π x, Σ y, f x = y),
            @sigma.mk _ (λg, f ∼ g)
              (λx, pr1 (k x)) (λx, pr2 (k x)) in
          let s := λ g h x, @sigma.mk _ (λy, f x = y) (g x) (h x) in
          have t1 : Πx, is_contr (Σ y, f x = y),
            from (λx, !is_contr_sigma_eq),
          have t2 : is_contr (Πx, Σ y, f x = y),
            from !wf,
          have t3 : (λ x, @sigma.mk _ (λ y, f x = y) (f x) idp) = s g h,
            from @center_eq (Π x, Σ y, f x = y) t2 _ _,
          have t4 : r (λ x, sigma.mk (f x) idp) = r (s g h),
            from ap r t3,
          have endt : sigma.mk f (homotopy.refl f) = sigma.mk g h,
            from t4,
          endt
        )
      )

  parameters (Q : Π g (h : f ∼ g), Type) (d : Q f (homotopy.refl f))

  definition homotopy_ind (g : Πx, B x) (h : f ∼ g) : Q g h :=
    @transport _ (λ gh, Q (pr1 gh) (pr2 gh)) (sigma.mk f (homotopy.refl f)) (sigma.mk g h)
      (@center_eq _ is_contr_sigma_homotopy _ _) d

  local attribute weak_funext [reducible]
  local attribute homotopy_ind [reducible]
  definition homotopy_ind_comp : homotopy_ind f (homotopy.refl f) = d :=
    (@hprop_eq_of_is_contr _ _ _ _ !center_eq idp)⁻¹ ▹ idp
end

-- Now the proof is fairly easy; we can just use the same induction principle on both sides.
universe variables l k

local attribute weak_funext [reducible]
theorem funext_of_weak_funext (wf : weak_funext.{l k}) : funext.{l k} :=
  λ A B f g,
    let eq_to_f := (λ g' x, f = g') in
    let sim2path := homotopy_ind f eq_to_f idp in
    assert t1 : sim2path f (homotopy.refl f) = idp,
      proof homotopy_ind_comp f eq_to_f idp qed,
    assert t2 : apd10 (sim2path f (homotopy.refl f)) = (homotopy.refl f),
      proof ap apd10 t1 qed,
    have sect : apd10 ∘ (sim2path g) ∼ id,
      proof (homotopy_ind f (λ g' x, apd10 (sim2path g' x) = x) t2) g qed,
    have retr : (sim2path g) ∘ apd10 ∼ id,
      from (λ h, eq.rec_on h (homotopy_ind_comp f _ idp)),
    is_equiv.adjointify apd10 (sim2path g) sect retr

definition funext_from_naive_funext : naive_funext -> funext :=
  compose funext_of_weak_funext weak_funext_of_naive_funext
