/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn
Ported from Coq HoTT

Theorems about sigma-types (dependent sums)
-/

import ..trunc .prod ..axioms.funext
open path sigma sigma.ops equiv is_equiv

namespace sigma
  infixr [local] ∘ := function.compose --remove
  variables {A A' : Type} {B : A → Type} {B' : A' → Type} {C : Πa, B a → Type}
            {D : Πa b, C a b → Type}
            {a a' a'' : A} {b b₁ b₂ : B a} {b' : B a'} {b'' : B a''} {u v w : Σa, B a}

  -- sigma.eta is already used for the eta rule for strict equality
  protected definition peta (u : Σa, B a) : ⟨u.1 , u.2⟩ ≈ u :=
  destruct u (λu1 u2, idp)

  definition eta2 (u : Σa b, C a b) : ⟨u.1, u.2.1, u.2.2⟩ ≈ u :=
  destruct u (λu1 u2, destruct u2 (λu21 u22, idp))

  definition eta3 (u : Σa b c, D a b c) : ⟨u.1, u.2.1, u.2.2.1, u.2.2.2⟩ ≈ u :=
  destruct u (λu1 u2, destruct u2 (λu21 u22, destruct u22 (λu221 u222, idp)))

  definition dpair_eq_dpair (p : a ≈ a') (q : p ▹ b ≈ b') : dpair a b ≈ dpair a' b' :=
  path.rec_on p (λb b' q, path.rec_on q idp) b b' q

  /- In Coq they often have to give u and v explicitly -/
  protected definition path (p : u.1 ≈ v.1) (q : p ▹ u.2 ≈ v.2) : u ≈ v :=
  destruct u
           (λu1 u2, destruct v (λ v1 v2, dpair_eq_dpair))
           p q

  /- Projections of paths from a total space -/

  definition path_pr1 (p : u ≈ v) : u.1 ≈ v.1 :=
  ap dpr1 p

  postfix `..1`:(max+1) := path_pr1

  definition path_pr2 (p : u ≈ v) : p..1 ▹ u.2 ≈ v.2 :=
  path.rec_on p idp
  --Coq uses the following proof, which only computes if u,v are dpairs AND p is idp
  --(transport_compose B dpr1 p u.2)⁻¹ ⬝ apD dpr2 p

  postfix `..2`:(max+1) := path_pr2

  definition dpair_sigma_path (p : u.1 ≈ v.1) (q : p ▹ u.2 ≈ v.2)
      :  dpair (sigma.path p q)..1 (sigma.path p q)..2 ≈ ⟨p, q⟩ :=
  begin
    reverts (p, q),
    apply (destruct u), intros (u1, u2),
    apply (destruct v), intros (v1, v2, p), generalize v2, --change to revert
    apply (path.rec_on p), intros (v2, q),
    apply (path.rec_on q), apply idp
  end

  definition sigma_path_pr1 (p : u.1 ≈ v.1) (q : p ▹ u.2 ≈ v.2) : (sigma.path p q)..1 ≈ p :=
  (!dpair_sigma_path)..1

  definition sigma_path_pr2 (p : u.1 ≈ v.1) (q : p ▹ u.2 ≈ v.2)
      : sigma_path_pr1 p q ▹ (sigma.path p q)..2 ≈ q :=
  (!dpair_sigma_path)..2

  definition sigma_path_eta (p : u ≈ v) : sigma.path (p..1) (p..2) ≈ p :=
  begin
    apply (path.rec_on p),
    apply (destruct u), intros (u1, u2),
    apply idp
  end

  definition transport_dpr1_sigma_path {B' : A → Type} (p : u.1 ≈ v.1) (q : p ▹ u.2 ≈ v.2)
      : transport (λx, B' x.1) (sigma.path p q) ≈ transport B' p :=
  begin
    reverts (p, q),
    apply (destruct u), intros (u1, u2),
    apply (destruct v), intros (v1, v2, p), generalize v2,
    apply (path.rec_on p), intros (v2, q),
    apply (path.rec_on q), apply idp
  end

  /- the uncurried version of sigma_path. We will prove that this is an equivalence -/

  definition sigma_path_uncurried (pq : Σ(p : dpr1 u ≈ dpr1 v), p ▹ (dpr2 u) ≈ dpr2 v) : u ≈ v :=
  destruct pq sigma.path

  definition dpair_sigma_path_uncurried (pq : Σ(p : u.1 ≈ v.1), p ▹ u.2 ≈ v.2)
      :  dpair (sigma_path_uncurried pq)..1 (sigma_path_uncurried pq)..2 ≈ pq :=
  destruct pq dpair_sigma_path

  definition sigma_path_pr1_uncurried (pq : Σ(p : u.1 ≈ v.1), p ▹ u.2 ≈ v.2)
      : (sigma_path_uncurried pq)..1 ≈ pq.1 :=
  (!dpair_sigma_path_uncurried)..1

  definition sigma_path_pr2_uncurried (pq : Σ(p : u.1 ≈ v.1), p ▹ u.2 ≈ v.2)
      : (sigma_path_pr1_uncurried pq) ▹ (sigma_path_uncurried pq)..2 ≈ pq.2 :=
  (!dpair_sigma_path_uncurried)..2

  definition sigma_path_eta_uncurried (p : u ≈ v) : sigma_path_uncurried (dpair p..1 p..2) ≈ p :=
  !sigma_path_eta

  definition transport_sigma_path_dpr1_uncurried {B' : A → Type}
    (pq : Σ(p : u.1 ≈ v.1), p ▹ u.2 ≈ v.2)
      : transport (λx, B' x.1) (@sigma_path_uncurried A B u v pq) ≈ transport B' pq.1 :=
  destruct pq transport_dpr1_sigma_path

  definition is_equiv_sigma_path [instance] (u v : Σa, B a)
      : is_equiv (@sigma_path_uncurried A B u v) :=
  adjointify sigma_path_uncurried
             (λp, ⟨p..1, p..2⟩)
             sigma_path_eta_uncurried
             dpair_sigma_path_uncurried

  definition equiv_sigma_path (u v : Σa, B a) : (Σ(p : u.1 ≈ v.1),  p ▹ u.2 ≈ v.2) ≃ (u ≈ v) :=
  equiv.mk sigma_path_uncurried !is_equiv_sigma_path

  definition dpair_eq_dpair_pp_pp (p1 : a  ≈ a' ) (q1 : p1 ▹ b  ≈ b' )
                                  (p2 : a' ≈ a'') (q2 : p2 ▹ b' ≈ b'') :
      dpair_eq_dpair (p1 ⬝ p2) (transport_pp B p1 p2 b ⬝ ap (transport B p2) q1 ⬝ q2)
    ≈ dpair_eq_dpair p1 q1 ⬝ dpair_eq_dpair  p2 q2 :=
  begin
    reverts (b', p2, b'', q1, q2),
    apply (path.rec_on p1), intros (b', p2),
    apply (path.rec_on p2), intros (b'', q1),
    apply (path.rec_on q1), intro q2,
    apply (path.rec_on q2), apply idp
  end

  definition sigma_path_pp_pp (p1 : u.1 ≈ v.1) (q1 : p1 ▹ u.2 ≈ v.2)
                              (p2 : v.1 ≈ w.1) (q2 : p2 ▹ v.2 ≈ w.2) :
      sigma.path (p1 ⬝ p2) (transport_pp B p1 p2 u.2 ⬝ ap (transport B p2) q1 ⬝ q2)
    ≈ sigma.path p1 q1 ⬝ sigma.path p2 q2 :=
  begin
    reverts (p1, q1, p2, q2),
    apply (destruct u), intros (u1, u2),
    apply (destruct v), intros (v1, v2),
    apply (destruct w), intros,
    apply dpair_eq_dpair_pp_pp
  end

  definition dpair_eq_dpair_p1_1p (p : a ≈ a') (q : p ▹ b ≈ b') :
      dpair_eq_dpair p q ≈ dpair_eq_dpair p idp ⬝ dpair_eq_dpair idp q :=
  begin
    reverts (b', q),
    apply (path.rec_on p), intros (b', q),
    apply (path.rec_on q), apply idp
  end

  /- path_pr1 commutes with the groupoid structure. -/

  definition path_pr1_idp (u : Σa, B a)           : (idpath u)..1 ≈ idpath (u.1)    := idp
  definition path_pr1_pp  (p : u ≈ v) (q : v ≈ w) : (p ⬝ q)   ..1 ≈ (p..1) ⬝ (q..1) := !ap_pp
  definition path_pr1_V   (p : u ≈ v)             : p⁻¹       ..1 ≈ (p..1)⁻¹        := !ap_V

  /- Applying dpair to one argument is the same as dpair_eq_dpair with reflexivity in the first place. -/

  definition ap_dpair (q : b₁ ≈ b₂) : ap (dpair a) q ≈ dpair_eq_dpair idp q :=
  path.rec_on q idp

  /- Dependent transport is the same as transport along a sigma_path. -/

  definition transportD_eq_transport (p : a ≈ a') (c : C a b) :
      p ▹D c ≈ transport (λu, C (u.1) (u.2)) (dpair_eq_dpair p idp) c :=
  path.rec_on p idp

  definition sigma_path_eq_sigma_path {p1 q1 : a ≈ a'} {p2 : p1 ▹ b ≈ b'} {q2 : q1 ▹ b ≈ b'}
      (r : p1 ≈ q1) (s : r ▹ p2 ≈ q2) : sigma.path p1 p2 ≈ sigma.path q1 q2 :=
  path.rec_on r
              proof (λq2 s, path.rec_on s idp) qed
              q2
              s
  -- begin
  --   reverts (q2, s),
  --   apply (path.rec_on r), intros (q2, s),
  --   apply (path.rec_on s), apply idp
  -- end


  /- A path between paths in a total space is commonly shown component wise. -/
  definition path_sigma_path {p q : u ≈ v} (r : p..1 ≈ q..1) (s : r ▹ p..2 ≈ q..2) : p ≈ q :=
  begin
    reverts (q, r, s),
    apply (path.rec_on p),
    apply (destruct u), intros (u1, u2, q, r, s),
    apply concat, rotate 1,
    apply sigma_path_eta,
    apply (sigma_path_eq_sigma_path r s)
  end

  /- In Coq they often have to give u and v explicitly when using the following definition -/
  definition path_sigma_path_uncurried {p q : u ≈ v}
      (rs : Σ(r : p..1 ≈ q..1), transport (λx, transport B x u.2 ≈ v.2) r p..2 ≈ q..2) : p ≈ q :=
  destruct rs path_sigma_path

  /- Transport -/

  /- The concrete description of transport in sigmas (and also pis) is rather trickier than in the other types.  In particular, these cannot be described just in terms of transport in simpler types; they require also the dependent transport [transportD].

  In particular, this indicates why `transport` alone cannot be fully defined by induction on the structure of types, although Id-elim/transportD can be (cf. Observational Type Theory).  A more thorough set of lemmas, along the lines of the present ones but dealing with Id-elim rather than just transport, might be nice to have eventually? -/

  definition transport_eq (p : a ≈ a') (bc : Σ(b : B a), C a b)
      : p ▹ bc ≈ ⟨p ▹ bc.1, p ▹D bc.2⟩ :=
  begin
    apply (path.rec_on p),
    apply (destruct bc), intros (b, c),
    apply idp
  end

  /- The special case when the second variable doesn't depend on the first is simpler. -/
  definition transport_eq_deg {B : Type} {C : A → B → Type} (p : a ≈ a') (bc : Σ(b : B), C a b)
      : p ▹ bc ≈ ⟨bc.1, p ▹ bc.2⟩ :=
  begin
    apply (path.rec_on p),
    apply (destruct bc), intros (b, c),
    apply idp
  end

  /- Or if the second variable contains a first component that doesn't depend on the first. -/

  definition transport_eq_4deg {C : A → Type} {D : Π a:A, B a → C a → Type} (p : a ≈ a')
      (bcd : Σ(b : B a) (c : C a), D a b c) : p ▹ bcd ≈ ⟨p ▹ bcd.1, p ▹ bcd.2.1, p ▹D2 bcd.2.2⟩ :=
  begin
    revert bcd,
    apply (path.rec_on p), intro bcd,
    apply (destruct bcd), intros (b, cd),
    apply (destruct cd), intros (c, d),
    apply idp
  end

  /- Functorial action -/
  variables (f : A → A') (g : Πa, B a → B' (f a))

  protected definition functor (u : Σa, B a) : Σa', B' a' :=
  ⟨f u.1, g u.1 u.2⟩

  /- Equivalences -/

  --TODO: remove explicit arguments of is_equiv
  definition is_equiv_functor [H1 : is_equiv f] [H2 : Π a, is_equiv (g a)]
      : is_equiv (functor f g) :=
  adjointify (functor f g)
             (functor (f⁻¹) (λ(a' : A') (b' : B' a'),
               ((g (f⁻¹ a'))⁻¹ (transport B' (retr f a'⁻¹) b'))))
  begin
    intro u',
    apply (destruct u'), intros (a', b'),
    apply (sigma.path (retr f a')),
    -- "rewrite retr (g (f⁻¹ a'))"
    apply concat, apply (ap (λx, (transport B' (retr f a') x))), apply (retr (g (f⁻¹ a'))),
    show retr f a' ▹ (((retr f a') ⁻¹) ▹ b') ≈ b',
    from transport_pV B' (retr f a') b'
  end
  begin
    intro u,
    apply (destruct u), intros (a, b),
    apply (sigma.path (sect f a)),
    show transport B (sect f a) (g (f⁻¹ (f a))⁻¹ (transport B' (retr f (f a)⁻¹) (g a b))) ≈ b,
    from calc
      transport B (sect f a) (g (f⁻¹ (f a))⁻¹ (transport B' (retr f (f a)⁻¹) (g a b)))
          ≈ g a⁻¹ (transport (B' ∘ f) (sect f a) (transport B' (retr f (f a)⁻¹) (g a b)))
              : ap_transport (sect f a) (λ a, g a⁻¹)
      ... ≈ g a⁻¹ (transport B' (ap f (sect f a)) (transport B' (retr f (f a)⁻¹) (g a b)))
              : ap (g a⁻¹) !transport_compose
      ... ≈ g a⁻¹ (transport B' (ap f (sect f a)) (transport B' (ap f (sect f a)⁻¹) (g a b)))
           : ap (λ x, g a⁻¹ (transport B' (ap f (sect f a)) (transport B' (x⁻¹) (g a b)))) (adj f a)
      ... ≈ g a⁻¹ (g a b) : transport_pV
      ... ≈ b : sect (g a) b
  end
    -- -- "rewrite ap_transport"
    -- apply concat, apply inverse, apply (ap_transport (sect f a) (λ a, g a⁻¹)),
    -- apply concat, apply (ap (g a⁻¹)),
    --   -- "rewrite transport_compose"
    --   apply concat, apply transport_compose,
    --   -- "rewrite adj"
    --   -- "rewrite transport_pV"
    -- apply sect,

  definition equiv_functor_of_is_equiv [H1 : is_equiv f] [H2 : Π a, is_equiv (g a)]
    : (Σa, B a) ≃ (Σa', B' a') :=
  equiv.mk (functor f g) !is_equiv_functor

  context --remove
  irreducible inv function.compose --remove
  definition equiv_functor (Hf : A ≃ A') (Hg : Π a, B a ≃ B' (to_fun Hf a)) :
      (Σa, B a) ≃ (Σa', B' a') :=
  equiv_functor_of_is_equiv (to_fun Hf) (λ a, to_fun (Hg a))
  end --remove

  definition equiv_functor_id {B' : A → Type} (Hg : Π a, B a ≃ B' a) : (Σa, B a) ≃ Σa, B' a :=
  equiv_functor equiv.refl Hg

  definition ap_functor_sigma_dpair (p : a ≈ a') (q : p ▹ b ≈ b')
    : ap (sigma.functor f g) (sigma.path p q)
    ≈ sigma.path (ap f p)
                 (transport_compose _ f p (g a b)⁻¹ ⬝ ap_transport p g b⁻¹ ⬝ ap (g a') q) :=
  begin
    reverts (b', q),
    apply (path.rec_on p),
    intros (b', q), apply (path.rec_on q),
    apply idp
  end

  definition ap_functor_sigma (p : u.1 ≈ v.1) (q : p ▹ u.2 ≈ v.2)
    : ap (sigma.functor f g) (sigma.path p q)
    ≈ sigma.path (ap f p)
                 (transport_compose B' f p (g u.1 u.2)⁻¹ ⬝ ap_transport p g u.2⁻¹ ⬝ ap (g v.1) q) :=
  begin
    reverts (p, q),
    apply (destruct u), intros (a, b),
    apply (destruct v), intros (a', b', p, q),
    apply ap_functor_sigma_dpair
  end

  /- definition 3.11.9(i): Summing up a contractible family of types does nothing. -/
  open truncation
  definition is_equiv_dpr1 [instance] (B : A → Type) [H : Π a, is_contr (B a)]
      : is_equiv (@dpr1 A B) :=
  adjointify dpr1
             (λa, ⟨a, !center⟩)
             (λa, idp)
             (λu, sigma.path idp !contr)

  definition equiv_of_all_contr [H : Π a, is_contr (B a)] : (Σa, B a) ≃ A :=
  equiv.mk dpr1 _

  /- definition 3.11.9(ii): Dually, summing up over a contractible type does nothing. -/

  definition equiv_center_of_contr (B : A → Type) [H : is_contr A] : (Σa, B a) ≃ B (center A)
  :=
  equiv.mk _ (adjointify
    (λu, contr u.1⁻¹ ▹ u.2)
    (λb, ⟨!center, b⟩)
    (λb, ap (λx, x ▹ b) !path2_contr)
    (λu, sigma.path !contr !transport_pV))

  /- Associativity -/

  --this proof is harder than in Coq because we don't have eta definitionally for sigma
  protected definition assoc_equiv (C : (Σa, B a) → Type) : (Σa b, C ⟨a, b⟩) ≃ (Σu, C u) :=
  -- begin
  --   apply equiv.mk,
  --   apply (adjointify (λav, ⟨⟨av.1, av.2.1⟩, av.2.2⟩)
  --                     (λuc, ⟨uc.1.1, uc.1.2, !peta⁻¹ ▹ uc.2⟩)),
  --     intro uc, apply (destruct uc), intro u,
  --               apply (destruct u), intros (a, b, c),
  --               apply idp,
  --     intro av, apply (destruct av), intros (a, v),
  --               apply (destruct v), intros (b, c),
  --               apply idp,
  -- end
  equiv.mk _ (adjointify
    (λav, ⟨⟨av.1, av.2.1⟩, av.2.2⟩)
    (λuc, ⟨uc.1.1, uc.1.2, !peta⁻¹ ▹ uc.2⟩)
    proof (λuc, destruct uc (λu, destruct u (λa b c, idp))) qed
    proof (λav, destruct av (λa v, destruct v (λb c, idp))) qed)

  open prod
  definition assoc_equiv_prod (C : (A × A') → Type) : (Σa a', C (a,a')) ≃ (Σu, C u) :=
  equiv.mk _ (adjointify
    (λav, ⟨(av.1, av.2.1), av.2.2⟩)
    (λuc, ⟨pr₁ (uc.1), pr₂ (uc.1), !prod.peta⁻¹ ▹ uc.2⟩)
    proof (λuc, destruct uc (λu, prod.destruct u (λa b c, idp))) qed
    proof (λav, destruct av (λa v, destruct v (λb c, idp))) qed)

  /- Symmetry -/
  definition symm_equiv_uncurried (C : A × A' → Type) : (Σa a', C (a, a')) ≃ (Σa' a, C (a, a')) :=
  calc
    (Σa a', C (a, a')) ≃ Σu, C u : assoc_equiv_prod
                 ... ≃ Σv, C (flip v) : equiv_functor !prod.symm_equiv
                                          (λu, prod.destruct u (λa a', equiv.refl))
                 ... ≃ (Σa' a, C (a, a')) : assoc_equiv_prod

  definition symm_equiv (C : A → A' → Type) : (Σa a', C a a') ≃ (Σa' a, C a a') :=
  symm_equiv_uncurried (λu, C (pr1 u) (pr2 u))

  definition equiv_prod (A B : Type) : (Σ(a : A), B) ≃ A × B :=
  equiv.mk _ (adjointify
    (λs, (s.1, s.2))
    (λp, ⟨pr₁ p, pr₂ p⟩)
    proof (λp, prod.destruct p (λa b, idp)) qed
    proof (λs, destruct s (λa b, idp)) qed)

  definition symm_equiv_deg (A B : Type) : (Σ(a : A), B) ≃ Σ(b : B), A :=
  calc
    (Σ(a : A), B) ≃ A × B : equiv_prod
              ... ≃ B × A : prod.symm_equiv
              ... ≃ Σ(b : B), A : equiv_prod

  /- ** Universal mapping properties -/
  /- *** The positive universal property. -/

  section
  open funext
  --in Coq this can be done without function extensionality
  definition is_equiv_sigma_rec [instance] [FUN : funext] (C : (Σa, B a) → Type)
    : is_equiv (@sigma.rec _ _ C) :=
  adjointify _ (λ g a b, g ⟨a, b⟩)
               (λ g, proof path_pi (λu, destruct u (λa b, idp)) qed)
               (λ f, idpath f)

  definition equiv_sigma_rec [FUN : funext] (C : (Σa, B a) → Type)
    : (Π(a : A) (b: B a), C ⟨a, b⟩) ≃ (Πxy, C xy) :=
  equiv.mk sigma.rec _

  /- *** The negative universal property. -/

  definition coind_uncurried (fg : Σ(f : Πa, B a), Πa, C a (f a)) (a : A) : Σ(b : B a), C a b
  := ⟨fg.1 a, fg.2 a⟩

  definition coind (f : Π a, B a) (g : Π a, C a (f a)) (a : A) : Σ(b : B a), C a b :=
  coind_uncurried ⟨f, g⟩ a

  --is the instance below dangerous?
  --in Coq this can be done without function extensionality
  definition is_equiv_coind [instance] [FUN : funext] (C : Πa, B a → Type)
    : is_equiv (@coind_uncurried _ _ C) :=
  adjointify _ (λ h, ⟨λa, (h a).1, λa, (h a).2⟩)
               (λ h, proof path_pi (λu, !peta) qed)
               (λfg, destruct fg (λ(f : Π (a : A), B a) (g : Π (x : A), C x (f x)), proof idp qed))

  definition equiv_coind [FUN : funext] : (Σ(f : Πa, B a), Πa, C a (f a)) ≃ (Πa, Σb, C a b) :=
  equiv.mk coind_uncurried _
  end

  /- ** Subtypes (sigma types whose second components are hprops) -/

  /- To prove equality in a subtype, we only need equality of the first component. -/
  definition path_hprop [H : Πa, is_hprop (B a)] (u v : Σa, B a) : u.1 ≈ v.1 → u ≈ v :=
  (sigma_path_uncurried ∘ (@inv _ _ dpr1 (@is_equiv_dpr1 _ _ (λp, !succ_is_trunc))))

  definition is_equiv_path_hprop [instance] [H : Πa, is_hprop (B a)] (u v : Σa, B a)
      : is_equiv (path_hprop u v) :=
  !is_equiv.compose

  definition equiv_path_hprop [H : Πa, is_hprop (B a)] (u v : Σa, B a) : (u.1 ≈ v.1) ≃ (u ≈ v)
  :=
  equiv.mk !path_hprop _

  /- truncatedness -/
  definition trunc_sigma [instance] (B : A → Type) (n : trunc_index)
      [HA : is_trunc n A] [HB : Πa, is_trunc n (B a)] : is_trunc n (Σa, B a) :=
  begin
  reverts (A, B, HA, HB),
  apply (trunc_index.rec_on n),
    intros (A, B, HA, HB),
      fapply trunc_equiv',
        apply equiv.symm,
          apply equiv_center_of_contr, apply HA, --should be solved by term synthesis
        apply HB,
     intros (n, IH, A, B, HA, HB),
       fapply is_trunc_succ, intros (u, v),
      fapply trunc_equiv',
         apply equiv_sigma_path,
         apply IH,
           apply succ_is_trunc, assumption,
           intro p,
             show is_trunc n (p ▹ u .2 ≈ v .2), from
             succ_is_trunc n (p ▹ u.2) (v.2),
  end

end sigma

open truncation sigma

namespace prod
  /- truncatedness -/
  definition trunc_prod [instance] (A B : Type) (n : trunc_index)
      [HA : is_trunc n A] [HB : is_trunc n B] : is_trunc n (A × B) :=
  trunc_equiv' n !equiv_prod
end prod
