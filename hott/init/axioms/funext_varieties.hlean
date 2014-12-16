-- Copyright (c) 2014 Jakob von Raumer. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Jakob von Raumer
-- Ported from Coq HoTT
prelude
import ..path ..trunc ..equiv .funext

open eq truncation sigma function

/- In hott.axioms.funext, we defined function extensionality to be the assertion
   that the map apD10 is an equivalence.   We now prove that this follows
   from a couple of weaker-looking forms of function extensionality.  We do
   require eta conversion, which Coq 8.4+ has judgmentally.

   This proof is originally due to Voevodsky; it has since been simplified
   by Peter Lumsdaine and Michael Shulman. -/

-- Naive funext is the simple assertion that pointwise equal functions are equal.
-- TODO think about universe levels
definition naive_funext :=
  Π {A : Type} {P : A → Type} (f g : Πx, P x), (f ∼ g) → f = g

-- Weak funext says that a product of contractible types is contractible.
definition weak_funext.{l k} :=
  Π {A : Type.{l}} (P : A → Type.{k}) [H: Πx, is_contr (P x)], is_contr (Πx, P x)

-- The obvious implications are Funext -> NaiveFunext -> WeakFunext
-- TODO: Get class inference to work locally
definition naive_funext_from_funext [F : funext] : naive_funext :=
  (λ A P f g h,
    have Fefg: is_equiv (@apD10 A P f g),
      from (@funext.ap F A P f g),
    have eq1 : _, from (@is_equiv.inv _ _ (@apD10 A P f g) Fefg h),
    eq1
  )

definition weak_funext_from_naive_funext : naive_funext → weak_funext :=
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

context
  universes l k
  parameters (wf : weak_funext.{l+1 k+1}) {A : Type.{l+1}} {B : A → Type.{k+1}} (f : Π x, B x)

  protected definition idhtpy : f ∼ f := (λ x, idp)

  definition contr_basedhtpy [instance] : is_contr (Σ (g : Π x, B x), f ∼ g) :=
    is_contr.mk (dpair f idhtpy)
      (λ dp, sigma.rec_on dp
        (λ (g : Π x, B x) (h : f ∼ g),
          let r := λ (k : Π x, Σ y, f x = y),
            @dpair _ (λg, f ∼ g)
              (λx, dpr1 (k x)) (λx, dpr2 (k x)) in
          let s := λ g h x, @dpair _ (λy, f x = y) (g x) (h x) in
          have t1 : Πx, is_contr (Σ y, f x = y),
            from (λx, !contr_basedpaths),
          have t2 : is_contr (Πx, Σ y, f x = y),
            from !wf,
          have t3 : (λ x, @dpair _ (λ y, f x = y) (f x) idp) = s g h,
            from @path_contr (Π x, Σ y, f x = y) t2 _ _,
          have t4 : r (λ x, dpair (f x) idp) = r (s g h),
            from ap r t3,
          have endt : dpair f idhtpy = dpair g h,
            from t4,
          endt
        )
      )

  parameters (Q : Π g (h : f ∼ g), Type) (d : Q f idhtpy)

  definition htpy_ind (g : Πx, B x) (h : f ∼ g) : Q g h :=
    @transport _ (λ gh, Q (dpr1 gh) (dpr2 gh)) (dpair f idhtpy) (dpair g h)
      (@path_contr _ contr_basedhtpy _ _) d

  definition htpy_ind_beta : htpy_ind f idhtpy = d :=
    (@path2_contr _ _ _ _ !path_contr idp)⁻¹ ▹ idp

end

-- Now the proof is fairly easy; we can just use the same induction principle on both sides.
universe variables l k

theorem funext_from_weak_funext (wf : weak_funext.{l+1 k+1}) : funext.{l+1 k+1} :=
  funext.mk (λ A B f g,
    let eq_to_f := (λ g' x, f = g') in
    let sim2path := htpy_ind _ f eq_to_f idp in
    have t1 : sim2path f (idhtpy f) = idp,
      proof htpy_ind_beta _ f eq_to_f idp qed,
    have t2 : apD10 (sim2path f (idhtpy f)) = (idhtpy f),
      proof ap apD10 t1 qed,
    have sect : apD10 ∘ (sim2path g) ∼ id,
      proof (htpy_ind _ f (λ g' x, apD10 (sim2path g' x) = x) t2) g qed,
    have retr : (sim2path g) ∘ apD10 ∼ id,
      from (λ h, eq.rec_on h (htpy_ind_beta _ f _ idp)),
    is_equiv.adjointify apD10 (sim2path g) sect retr)

definition funext_from_naive_funext : naive_funext -> funext :=
  compose funext_from_weak_funext weak_funext_from_naive_funext
