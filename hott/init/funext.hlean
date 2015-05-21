/-
Copyright (c) 2014 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer

Ported from Coq HoTT
-/

prelude
import .trunc .equiv .ua
open eq is_trunc sigma function is_equiv equiv prod unit prod.ops

/-
   We now prove that funext follows from a couple of weaker-looking forms
   of function extensionality.

   This proof is originally due to Voevodsky; it has since been simplified
   by Peter Lumsdaine and Michael Shulman.
-/

definition funext.{l k} :=
  Π ⦃A : Type.{l}⦄ {P : A → Type.{k}} (f g : Π x, P x), is_equiv (@apd10 A P f g)

-- Naive funext is the simple assertion that pointwise equal functions are equal.
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
        from (λx, center_eq (f x)),
      have eq : (λx, center (P x)) = f,
        from nf A P (λx, center (P x)) f eq',
      eq
    )
  )

/-
  The less obvious direction is that weak_funext implies funext
  (and hence all three are logically equivalent).  The point is that under weak
  funext, the space of "pointwise homotopies" has the same universal property as
  the space of paths.
-/

section
  universe variables l k
  parameters [wf : weak_funext.{l k}] {A : Type.{l}} {B : A → Type.{k}} (f : Π x, B x)

  definition is_contr_sigma_homotopy : is_contr (Σ (g : Π x, B x), f ∼ g) :=
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
            from @eq_of_is_contr (Π x, Σ y, f x = y) t2 _ _,
          have t4 : r (λ x, sigma.mk (f x) idp) = r (s g h),
            from ap r t3,
          have endt : sigma.mk f (homotopy.refl f) = sigma.mk g h,
            from t4,
          endt
        )
      )
  local attribute is_contr_sigma_homotopy [instance]

  parameters (Q : Π g (h : f ∼ g), Type) (d : Q f (homotopy.refl f))

  definition homotopy_ind (g : Πx, B x) (h : f ∼ g) : Q g h :=
    @transport _ (λ gh, Q (pr1 gh) (pr2 gh)) (sigma.mk f (homotopy.refl f)) (sigma.mk g h)
      (@eq_of_is_contr _ is_contr_sigma_homotopy _ _) d

  local attribute weak_funext [reducible]
  local attribute homotopy_ind [reducible]
  definition homotopy_ind_comp : homotopy_ind f (homotopy.refl f) = d :=
    (@hprop_eq_of_is_contr _ _ _ _ !eq_of_is_contr idp)⁻¹ ▸ idp
end

/- Now the proof is fairly easy; we can just use the same induction principle on both sides. -/
section
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
    have left_inv : apd10 ∘ (sim2path g) ∼ id,
      proof (homotopy_ind f (λ g' x, apd10 (sim2path g' x) = x) t2) g qed,
    have right_inv : (sim2path g) ∘ apd10 ∼ id,
      from (λ h, eq.rec_on h (homotopy_ind_comp f _ idp)),
    is_equiv.adjointify apd10 (sim2path g) left_inv right_inv

definition funext_from_naive_funext : naive_funext → funext :=
  compose funext_of_weak_funext weak_funext_of_naive_funext
end

section
  universe variables l

  private theorem ua_isequiv_postcompose {A B : Type.{l}} {C : Type}
      {w : A → B} [H0 : is_equiv w] : is_equiv (@compose C A B w) :=
    let w' := equiv.mk w H0 in
    let eqinv : A = B := ((@is_equiv.inv _ _ _ (univalence A B)) w') in
    let eq' := equiv_of_eq eqinv in
    is_equiv.adjointify (@compose C A B w)
      (@compose C B A (is_equiv.inv w))
      (λ (x : C → B),
        have eqretr : eq' = w',
          from (@right_inv _ _ (@equiv_of_eq A B) (univalence A B) w'),
        have invs_eq : (to_fun eq')⁻¹ = (to_fun w')⁻¹,
          from inv_eq eq' w' eqretr,
        have eqfin : (to_fun eq') ∘ ((to_fun eq')⁻¹ ∘ x) = x,
          from (λ p,
            (@eq.rec_on Type.{l} A
              (λ B' p', Π (x' : C → B'), (to_fun (equiv_of_eq p'))
                ∘ ((to_fun (equiv_of_eq p'))⁻¹ ∘ x') = x')
              B p (λ x', idp))
            ) eqinv x,
        have eqfin' : (to_fun w') ∘ ((to_fun eq')⁻¹ ∘ x) = x,
          from eqretr ▸ eqfin,
        have eqfin'' : (to_fun w') ∘ ((to_fun w')⁻¹ ∘ x) = x,
          from invs_eq ▸ eqfin',
        eqfin''
      )
      (λ (x : C → A),
        have eqretr : eq' = w',
          from (@right_inv _ _ (@equiv_of_eq A B) (univalence A B) w'),
        have invs_eq : (to_fun eq')⁻¹ = (to_fun w')⁻¹,
          from inv_eq eq' w' eqretr,
        have eqfin : (to_fun eq')⁻¹ ∘ ((to_fun eq') ∘ x) = x,
          from (λ p, eq.rec_on p idp) eqinv,
        have eqfin' : (to_fun eq')⁻¹ ∘ ((to_fun w') ∘ x) = x,
          from eqretr ▸ eqfin,
        have eqfin'' : (to_fun w')⁻¹ ∘ ((to_fun w') ∘ x) = x,
          from invs_eq ▸ eqfin',
        eqfin''
      )

  -- We are ready to prove functional extensionality,
  -- starting with the naive non-dependent version.
  private definition diagonal [reducible] (B : Type) : Type
    := Σ xy : B × B, pr₁ xy = pr₂ xy

  private definition isequiv_src_compose {A B : Type}
      : @is_equiv (A → diagonal B)
                 (A → B)
                 (compose (pr₁ ∘ pr1)) :=
    @ua_isequiv_postcompose _ _ _ (pr₁ ∘ pr1)
        (is_equiv.adjointify (pr₁ ∘ pr1)
          (λ x, sigma.mk (x , x) idp) (λx, idp)
          (λ x, sigma.rec_on x
            (λ xy, prod.rec_on xy
              (λ b c p, eq.rec_on p idp))))

  private definition isequiv_tgt_compose {A B : Type}
      : @is_equiv (A → diagonal B)
                 (A → B)
                 (compose (pr₂ ∘ pr1)) :=
    @ua_isequiv_postcompose _ _ _ (pr2 ∘ pr1)
        (is_equiv.adjointify (pr2 ∘ pr1)
          (λ x, sigma.mk (x , x) idp) (λx, idp)
          (λ x, sigma.rec_on x
            (λ xy, prod.rec_on xy
              (λ b c p, eq.rec_on p idp))))

  set_option class.conservative false
  theorem nondep_funext_from_ua {A : Type} {B : Type}
      : Π {f g : A → B}, f ∼ g → f = g :=
    (λ (f g : A → B) (p : f ∼ g),
        let d := λ (x : A), sigma.mk (f x , f x) idp in
        let e := λ (x : A), sigma.mk (f x , g x) (p x) in
        let precomp1 :=  compose (pr₁ ∘ pr1) in
        have equiv1 [visible] : is_equiv precomp1,
          from @isequiv_src_compose A B,
        have equiv2 [visible] : Π x y, is_equiv (ap precomp1),
          from is_equiv.is_equiv_ap precomp1,
        have H' : Π (x y : A → diagonal B),
            pr₁ ∘ pr1 ∘ x = pr₁ ∘ pr1 ∘ y → x = y,
          from (λ x y, is_equiv.inv (ap precomp1)),
        have eq2 : pr₁ ∘ pr1 ∘ d = pr₁ ∘ pr1 ∘ e,
          from idp,
        have eq0 : d = e,
          from H' d e eq2,
        have eq1 : (pr₂ ∘ pr1) ∘ d = (pr₂ ∘ pr1) ∘ e,
          from ap _ eq0,
        eq1
    )

end

-- Now we use this to prove weak funext, which as we know
-- implies (with dependent eta) also the strong dependent funext.
theorem weak_funext_of_ua : weak_funext :=
  (λ (A : Type) (P : A → Type) allcontr,
    let U := (λ (x : A), unit) in
  have pequiv : Π (x : A), P x ≃ U x,
    from (λ x, @equiv_unit_of_is_contr (P x) (allcontr x)),
  have psim : Π (x : A), P x = U x,
    from (λ x, @is_equiv.inv _ _
      equiv_of_eq (univalence _ _) (pequiv x)),
  have p : P = U,
    from @nondep_funext_from_ua A Type P U psim,
  have tU' : is_contr (A → unit),
    from is_contr.mk (λ x, ⋆)
      (λ f, @nondep_funext_from_ua A unit (λ x, ⋆) f
        (λ x, unit.rec_on (f x) idp)),
  have tU : is_contr (Π x, U x),
    from tU',
  have tlast : is_contr (Πx, P x),
    from eq.transport _ p⁻¹ tU,
  tlast
)

-- In the following we will proof function extensionality using the univalence axiom
definition funext_of_ua : funext :=
  funext_of_weak_funext (@weak_funext_of_ua)

variables {A : Type} {P : A → Type} {f g : Π x, P x}

namespace funext
  definition is_equiv_apd [instance] (f g : Π x, P x) : is_equiv (@apd10 A P f g) :=
  funext_of_ua f g
end funext

open funext

definition eq_equiv_homotopy : (f = g) ≃ (f ∼ g) :=
equiv.mk apd10 _

definition eq_of_homotopy [reducible] : f ∼ g → f = g :=
(@apd10 A P f g)⁻¹

--TODO: rename to eq_of_homotopy_idp
definition eq_of_homotopy_idp (f : Π x, P x) : eq_of_homotopy (λx : A, idpath (f x)) = idpath f :=
is_equiv.left_inv apd10 idp

definition naive_funext_of_ua : naive_funext :=
λ A P f g h, eq_of_homotopy h

protected definition homotopy.rec_on [recursor] {Q : (f ∼ g) → Type} (p : f ∼ g)
  (H : Π(q : f = g), Q (apd10 q)) : Q p :=
right_inv apd10 p ▸ H (eq_of_homotopy p)
