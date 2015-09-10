/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jakob von Raumer
-/

import .iso types.pi

open function category eq prod prod.ops equiv is_equiv sigma sigma.ops is_trunc funext iso
open pi

structure functor (C D : Precategory) : Type :=
  (to_fun_ob : C → D)
  (to_fun_hom : Π ⦃a b : C⦄, hom a b → hom (to_fun_ob a) (to_fun_ob b))
  (respect_id : Π (a : C), to_fun_hom (ID a) = ID (to_fun_ob a))
  (respect_comp : Π {a b c : C} (g : hom b c) (f : hom a b),
    to_fun_hom (g ∘ f) = to_fun_hom g ∘ to_fun_hom f)

namespace functor

  infixl `⇒`:25 := functor
  variables {A B C D E : Precategory}

  attribute to_fun_ob [coercion]
  attribute to_fun_hom [coercion]

  -- The following lemmas will later be used to prove that the type of
  -- precategories forms a precategory itself
  protected definition compose [reducible] [constructor] (G : functor D E) (F : functor C D)
    : functor C E :=
  functor.mk
    (λ x, G (F x))
    (λ a b f, G (F f))
    (λ a, abstract calc
      G (F (ID a)) = G (ID (F a)) : by rewrite respect_id
               ... = ID (G (F a)) : by rewrite respect_id end)
    (λ a b c g f, abstract calc
      G (F (g ∘ f)) = G (F g ∘ F f)     : by rewrite respect_comp
                ... = G (F g) ∘ G (F f) : by rewrite respect_comp end)

  infixr `∘f`:60 := functor.compose

  protected definition id [reducible] [constructor] {C : Precategory} : functor C C :=
  mk (λa, a) (λ a b f, f) (λ a, idp) (λ a b c f g, idp)

  protected definition ID [reducible] [constructor] (C : Precategory) : functor C C := @functor.id C
  notation 1 := functor.id

  definition functor_mk_eq' {F₁ F₂ : C → D} {H₁ : Π(a b : C), hom a b → hom (F₁ a) (F₁ b)}
    {H₂ : Π(a b : C), hom a b → hom (F₂ a) (F₂ b)} (id₁ id₂ comp₁ comp₂)
    (pF : F₁ = F₂) (pH : pF ▸ H₁ = H₂)
      : functor.mk F₁ H₁ id₁ comp₁ = functor.mk F₂ H₂ id₂ comp₂ :=
  apd01111 functor.mk pF pH !is_hprop.elim !is_hprop.elim

  definition functor_eq' {F₁ F₂ : C ⇒ D}
    : Π(p : to_fun_ob F₁ = to_fun_ob F₂),
          (transport (λx, Πa b f, hom (x a) (x b)) p (to_fun_hom F₁) = to_fun_hom F₂) → F₁ = F₂ :=
  by induction F₁; induction F₂; apply functor_mk_eq'

  definition functor_mk_eq {F₁ F₂ : C → D} {H₁ : Π(a b : C), hom a b → hom (F₁ a) (F₁ b)}
    {H₂ : Π(a b : C), hom a b → hom (F₂ a) (F₂ b)} (id₁ id₂ comp₁ comp₂) (pF : F₁ ~ F₂)
    (pH : Π(a b : C) (f : hom a b), hom_of_eq (pF b) ∘ H₁ a b f ∘ inv_of_eq (pF a) = H₂ a b f)
      : functor.mk F₁ H₁ id₁ comp₁ = functor.mk F₂ H₂ id₂ comp₂ :=
  begin
    fapply functor_mk_eq',
    { exact eq_of_homotopy pF},
    { refine eq_of_homotopy (λc, eq_of_homotopy (λc', eq_of_homotopy (λf, _))), intros,
      rewrite [+pi_transport_constant,-pH,-transport_hom]}
  end

  definition functor_eq {F₁ F₂ : C ⇒ D} : Π(p : to_fun_ob F₁ ~ to_fun_ob F₂),
    (Π(a b : C) (f : hom a b), hom_of_eq (p b) ∘ F₁ f ∘ inv_of_eq (p a) = F₂ f) → F₁ = F₂ :=
  by induction F₁; induction F₂; apply functor_mk_eq

  definition functor_mk_eq_constant {F : C → D} {H₁ : Π(a b : C), hom a b → hom (F a) (F b)}
    {H₂ : Π(a b : C), hom a b → hom (F a) (F b)} (id₁ id₂ comp₁ comp₂)
    (pH : Π(a b : C) (f : hom a b), H₁ a b f = H₂ a b f)
      : functor.mk F H₁ id₁ comp₁ = functor.mk F H₂ id₂ comp₂ :=
  functor_eq (λc, idp) (λa b f, !id_leftright ⬝ !pH)

  definition preserve_is_iso [constructor] (F : C ⇒ D) {a b : C} (f : hom a b) [H : is_iso f]
    : is_iso (F f) :=
  begin
    fapply @is_iso.mk, apply (F (f⁻¹)),
    repeat (apply concat ; symmetry ;  apply (respect_comp F) ;
      apply concat ; apply (ap (λ x, to_fun_hom F x)) ;
      (apply iso.left_inverse | apply iso.right_inverse);
      apply (respect_id F) ),
  end

  theorem respect_inv (F : C ⇒ D) {a b : C} (f : hom a b) [H : is_iso f] [H' : is_iso (F f)] :
    F (f⁻¹) = (F f)⁻¹ :=
  begin
    fapply @left_inverse_eq_right_inverse, apply (F f),
      transitivity to_fun_hom F (f⁻¹ ∘ f),
        {symmetry, apply (respect_comp F)},
        {transitivity to_fun_hom F category.id,
          {congruence, apply iso.left_inverse},
          {apply respect_id}},
      apply iso.right_inverse
  end

  attribute preserve_is_iso [instance] [priority 100]

  definition to_fun_iso [constructor] (F : C ⇒ D) {a b : C} (f : a ≅ b) : F a ≅ F b :=
  iso.mk (F f)

  theorem respect_inv' (F : C ⇒ D) {a b : C} (f : hom a b) {H : is_iso f} : F (f⁻¹) = (F f)⁻¹ :=
  respect_inv F f

  theorem respect_refl (F : C ⇒ D) (a : C) : to_fun_iso F (iso.refl a) = iso.refl (F a) :=
  iso_eq !respect_id

  theorem respect_symm (F : C ⇒ D) {a b : C} (f : a ≅ b)
    : to_fun_iso F f⁻¹ⁱ = (to_fun_iso F f)⁻¹ⁱ :=
  iso_eq !respect_inv

  theorem respect_trans (F : C ⇒ D) {a b c : C} (f : a ≅ b) (g : b ≅ c)
    : to_fun_iso F (f ⬝i g) = to_fun_iso F f ⬝i to_fun_iso F g :=
  iso_eq !respect_comp

  protected definition assoc (H : C ⇒ D) (G : B ⇒ C) (F : A ⇒ B) :
      H ∘f (G ∘f F) = (H ∘f G) ∘f F :=
  !functor_mk_eq_constant (λa b f, idp)

  protected definition id_left  (F : C ⇒ D) : 1 ∘f F = F :=
  functor.rec_on F (λF1 F2 F3 F4, !functor_mk_eq_constant (λa b f, idp))

  protected definition id_right (F : C ⇒ D) : F ∘f 1 = F :=
  functor.rec_on F (λF1 F2 F3 F4, !functor_mk_eq_constant (λa b f, idp))

  protected definition comp_id_eq_id_comp (F : C ⇒ D) : F ∘f 1 = 1 ∘f F :=
  !functor.id_right ⬝ !functor.id_left⁻¹

  -- "functor C D" is equivalent to a certain sigma type
  protected definition sigma_char :
    (Σ (to_fun_ob : C → D)
    (to_fun_hom : Π ⦃a b : C⦄, hom a b → hom (to_fun_ob a) (to_fun_ob b)),
    (Π (a : C), to_fun_hom (ID a) = ID (to_fun_ob a)) ×
    (Π {a b c : C} (g : hom b c) (f : hom a b),
      to_fun_hom (g ∘ f) = to_fun_hom g ∘ to_fun_hom f)) ≃ (functor C D) :=
  begin
    fapply equiv.MK,
      {intro S, fapply functor.mk,
        exact (S.1), exact (S.2.1),
        -- TODO(Leo): investigate why we need to use relaxed-exact (rexact) tactic here
        exact (pr₁ S.2.2), rexact (pr₂ S.2.2)},
      {intro F, cases F with d1 d2 d3 d4, exact ⟨d1, d2, (d3, @d4)⟩},
      {intro F, cases F, reflexivity},
      {intro S, cases S with d1 S2, cases S2 with d2 P1, cases P1, reflexivity},
  end

  section
    local attribute precategory.is_hset_hom [priority 1001]
    protected theorem is_hset_functor [instance]
      [HD : is_hset D] : is_hset (functor C D) :=
    by apply is_trunc_equiv_closed; apply functor.sigma_char
  end

  definition functor_mk_eq'_idp (F : C → D) (H : Π(a b : C), hom a b → hom (F a) (F b))
    (id comp) : functor_mk_eq' id id comp comp (idpath F) (idpath H) = idp :=
  begin
    fapply (apd011 (apd01111 functor.mk idp idp)),
    apply is_hset.elim,
    apply is_hset.elim
  end

  definition functor_eq'_idp (F : C ⇒ D) : functor_eq' idp idp = (idpath F) :=
  by (cases F; apply functor_mk_eq'_idp)

  definition functor_eq_eta' {F₁ F₂ : C ⇒ D} (p : F₁ = F₂)
      : functor_eq' (ap to_fun_ob p) (!tr_compose⁻¹ ⬝ apd to_fun_hom p) = p :=
  begin
    cases p, cases F₁,
    apply concat, rotate_left 1, apply functor_eq'_idp,
    esimp
  end

  theorem functor_eq2' {F₁ F₂ : C ⇒ D} {p₁ p₂ : to_fun_ob F₁ = to_fun_ob F₂} (q₁ q₂)
    (r : p₁ = p₂) : functor_eq' p₁ q₁ = functor_eq' p₂ q₂ :=
  by cases r; apply (ap (functor_eq' p₂)); apply is_hprop.elim

  theorem functor_eq2 {F₁ F₂ : C ⇒ D} (p q : F₁ = F₂) (r : ap010 to_fun_ob p ~ ap010 to_fun_ob q)
    : p = q :=
  begin
    cases F₁ with ob₁ hom₁ id₁ comp₁,
    cases F₂ with ob₂ hom₂ id₂ comp₂,
    rewrite [-functor_eq_eta' p, -functor_eq_eta' q],
    apply functor_eq2',
    apply ap_eq_ap_of_homotopy,
    exact r,
  end

  theorem ap010_apd01111_functor {F₁ F₂ : C → D} {H₁ : Π(a b : C), hom a b → hom (F₁ a) (F₁ b)}
    {H₂ : Π(a b : C), hom a b → hom (F₂ a) (F₂ b)} {id₁ id₂ comp₁ comp₂}
    (pF : F₁ = F₂) (pH : pF ▸ H₁ = H₂) (pid : cast (apd011 _ pF pH) id₁ = id₂)
    (pcomp : cast (apd0111 _ pF pH pid) comp₁ = comp₂) (c : C)
      : ap010 to_fun_ob (apd01111 functor.mk pF pH pid pcomp) c = ap10 pF c :=
  by induction pF; induction pH; induction pid; induction pcomp; reflexivity

  definition ap010_functor_eq {F₁ F₂ : C ⇒ D} (p : to_fun_ob F₁ ~ to_fun_ob F₂)
    (q : (λ(a b : C) (f : hom a b), hom_of_eq (p b) ∘ F₁ f ∘ inv_of_eq (p a)) ~3 to_fun_hom F₂) (c : C) :
    ap010 to_fun_ob (functor_eq p q) c = p c :=
  begin
    cases F₁ with F₁o F₁h F₁id F₁comp, cases F₂ with F₂o F₂h F₂id F₂comp,
    esimp [functor_eq,functor_mk_eq,functor_mk_eq'],
    rewrite [ap010_apd01111_functor,↑ap10,{apd10 (eq_of_homotopy p)}right_inv apd10]
  end

  definition ap010_functor_mk_eq_constant {F : C → D} {H₁ : Π(a b : C), hom a b → hom (F a) (F b)}
    {H₂ : Π(a b : C), hom a b → hom (F a) (F b)} {id₁ id₂ comp₁ comp₂}
    (pH : Π(a b : C) (f : hom a b), H₁ a b f = H₂ a b f) (c : C) :
  ap010 to_fun_ob (functor_mk_eq_constant id₁ id₂ comp₁ comp₂ pH) c = idp :=
  !ap010_functor_eq

  definition ap010_assoc (H : C ⇒ D) (G : B ⇒ C) (F : A ⇒ B) (a : A) :
    ap010 to_fun_ob (functor.assoc H G F) a = idp :=
  by apply ap010_functor_mk_eq_constant

  definition compose_pentagon (K : D ⇒ E) (H : C ⇒ D) (G : B ⇒ C) (F : A ⇒ B) :
    (calc K ∘f H ∘f G ∘f F = (K ∘f H) ∘f G ∘f F : functor.assoc
      ... = ((K ∘f H) ∘f G) ∘f F : functor.assoc)
    =
    (calc K ∘f H ∘f G ∘f F = K ∘f (H ∘f G) ∘f F : ap (λx, K ∘f x) !functor.assoc
      ... = (K ∘f H ∘f G) ∘f F : functor.assoc
      ... = ((K ∘f H) ∘f G) ∘f F : ap (λx, x ∘f F) !functor.assoc) :=
  begin
  have lem1  : Π{F₁ F₂ : A ⇒ D} (p : F₁ = F₂) (a : A),
    ap010 to_fun_ob (ap (λx, K ∘f x) p) a = ap (to_fun_ob K) (ap010 to_fun_ob p a),
      by intros; cases p; esimp,
  have lem2 : Π{F₁ F₂ : B ⇒ E} (p : F₁ = F₂) (a : A),
    ap010 to_fun_ob (ap (λx, x ∘f F) p) a = ap010 to_fun_ob p (F a),
      by intros; cases p; esimp,
  apply functor_eq2,
  intro a, esimp,
  rewrite [+ap010_con,lem1,lem2,
            ap010_assoc K H (G ∘f F) a,
            ap010_assoc (K ∘f H) G F a,
            ap010_assoc H G F a,
            ap010_assoc K H G (F a),
            ap010_assoc K (H ∘f G) F a],
  end

end functor
