/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: types.sigma
Author: Floris van Doorn

Ported from Coq HoTT
Theorems about sigma-types (dependent sums)
-/

import types.prod

open eq sigma sigma.ops equiv is_equiv

namespace sigma
  local infixr ∘ := function.compose --remove
  variables {A A' : Type} {B : A → Type} {B' : A' → Type} {C : Πa, B a → Type}
            {D : Πa b, C a b → Type}
            {a a' a'' : A} {b b₁ b₂ : B a} {b' : B a'} {b'' : B a''} {u v w : Σa, B a}

  protected definition eta : Π (u : Σa, B a), ⟨u.1 , u.2⟩ = u
  | eta ⟨u₁, u₂⟩ := idp

  definition eta2 : Π (u : Σa b, C a b), ⟨u.1, u.2.1, u.2.2⟩ = u
  | eta2 ⟨u₁, u₂, u₃⟩ := idp

  definition eta3 : Π (u : Σa b c, D a b c), ⟨u.1, u.2.1, u.2.2.1, u.2.2.2⟩ = u
  | eta3 ⟨u₁, u₂, u₃, u₄⟩ := idp

  definition dpair_eq_dpair (p : a = a') (q : p ▹ b = b') : ⟨a, b⟩ = ⟨a', b'⟩ :=
  by cases p; cases q; apply idp

  definition sigma_eq (p : u.1 = v.1) (q : p ▹ u.2 = v.2) : u = v :=
  by cases u; cases v; apply (dpair_eq_dpair p q)

  /- Projections of paths from a total space -/

  definition eq_pr1 (p : u = v) : u.1 = v.1 :=
  ap pr1 p

  postfix `..1`:(max+1) := eq_pr1

  definition eq_pr2 (p : u = v) : p..1 ▹ u.2 = v.2 :=
  by cases p; apply idp

  postfix `..2`:(max+1) := eq_pr2

  private definition dpair_sigma_eq (p : u.1 = v.1) (q : p ▹ u.2 = v.2)
      : ⟨(sigma_eq p q)..1, (sigma_eq p q)..2⟩ = ⟨p, q⟩ :=
  by cases u; cases v; cases p; cases q; apply idp

  definition sigma_eq_pr1 (p : u.1 = v.1) (q : p ▹ u.2 = v.2) : (sigma_eq p q)..1 = p :=
  (dpair_sigma_eq p q)..1

  definition sigma_eq_pr2 (p : u.1 = v.1) (q : p ▹ u.2 = v.2)
      : sigma_eq_pr1 p q ▹ (sigma_eq p q)..2 = q :=
  (dpair_sigma_eq p q)..2

  definition sigma_eq_eta (p : u = v) : sigma_eq (p..1) (p..2) = p :=
  by cases p; cases u; apply idp

  definition tr_pr1_sigma_eq {B' : A → Type} (p : u.1 = v.1) (q : p ▹ u.2 = v.2)
      : transport (λx, B' x.1) (sigma_eq p q) = transport B' p :=
  by cases u; cases v; cases p; cases q; apply idp

  /- the uncurried version of sigma_eq. We will prove that this is an equivalence -/

  definition sigma_eq_uncurried : Π (pq : Σ(p : u.1 = v.1), p ▹ u.2 = v.2), u = v
  | sigma_eq_uncurried ⟨pq₁, pq₂⟩ := sigma_eq pq₁ pq₂

  definition dpair_sigma_eq_uncurried : Π (pq : Σ(p : u.1 = v.1), p ▹ u.2 = v.2),
        ⟨(sigma_eq_uncurried pq)..1, (sigma_eq_uncurried pq)..2⟩ = pq
  | dpair_sigma_eq_uncurried ⟨pq₁, pq₂⟩ := dpair_sigma_eq pq₁ pq₂

  definition sigma_eq_pr1_uncurried (pq : Σ(p : u.1 = v.1), p ▹ u.2 = v.2)
      : (sigma_eq_uncurried pq)..1 = pq.1 :=
  (dpair_sigma_eq_uncurried pq)..1

  definition sigma_eq_pr2_uncurried (pq : Σ(p : u.1 = v.1), p ▹ u.2 = v.2)
      : (sigma_eq_pr1_uncurried pq) ▹ (sigma_eq_uncurried pq)..2 = pq.2 :=
  (dpair_sigma_eq_uncurried pq)..2

  definition sigma_eq_eta_uncurried (p : u = v) : sigma_eq_uncurried ⟨p..1, p..2⟩ = p :=
  sigma_eq_eta p

  definition tr_sigma_eq_pr1_uncurried {B' : A → Type}
    (pq : Σ(p : u.1 = v.1), p ▹ u.2 = v.2)
      : transport (λx, B' x.1) (@sigma_eq_uncurried A B u v pq) = transport B' pq.1 :=
  destruct pq tr_pr1_sigma_eq

  definition is_equiv_sigma_eq [instance] (u v : Σa, B a)
      : is_equiv (@sigma_eq_uncurried A B u v) :=
  adjointify sigma_eq_uncurried
             (λp, ⟨p..1, p..2⟩)
             sigma_eq_eta_uncurried
             dpair_sigma_eq_uncurried

  definition equiv_sigma_eq (u v : Σa, B a) : (Σ(p : u.1 = v.1),  p ▹ u.2 = v.2) ≃ (u = v) :=
  equiv.mk sigma_eq_uncurried !is_equiv_sigma_eq

  definition dpair_eq_dpair_con (p1 : a  = a' ) (q1 : p1 ▹ b  = b' )
                                  (p2 : a' = a'') (q2 : p2 ▹ b' = b'') :
      dpair_eq_dpair (p1 ⬝ p2) (tr_con B p1 p2 b ⬝ ap (transport B p2) q1 ⬝ q2)
    = dpair_eq_dpair p1 q1 ⬝ dpair_eq_dpair  p2 q2 :=
  by cases p1; cases p2; cases q1; cases q2; apply idp

  definition sigma_eq_con (p1 : u.1 = v.1) (q1 : p1 ▹ u.2 = v.2)
                              (p2 : v.1 = w.1) (q2 : p2 ▹ v.2 = w.2) :
      sigma_eq (p1 ⬝ p2) (tr_con B p1 p2 u.2 ⬝ ap (transport B p2) q1 ⬝ q2)
    = sigma_eq p1 q1 ⬝ sigma_eq p2 q2 :=
  by cases u; cases v; cases w; apply dpair_eq_dpair_con

  local attribute dpair_eq_dpair [reducible]
  definition dpair_eq_dpair_con_idp (p : a = a') (q : p ▹ b = b') :
      dpair_eq_dpair p q = dpair_eq_dpair p idp ⬝ dpair_eq_dpair idp q :=
  by cases p; cases q; apply idp

  /- eq_pr1 commutes with the groupoid structure. -/

  definition eq_pr1_idp (u : Σa, B a)           : (refl u) ..1 = refl (u.1)      := idp
  definition eq_pr1_con  (p : u = v) (q : v = w) : (p ⬝ q)  ..1 = (p..1) ⬝ (q..1) := !ap_con
  definition eq_pr1_inv   (p : u = v)             : p⁻¹      ..1 = (p..1)⁻¹        := !ap_inv

  /- Applying dpair to one argument is the same as dpair_eq_dpair with reflexivity in the first place. -/

  definition ap_dpair (q : b₁ = b₂) : ap (sigma.mk a) q = dpair_eq_dpair idp q :=
  by cases q; apply idp

  /- Dependent transport is the same as transport along a sigma_eq. -/

  definition transportD_eq_transport (p : a = a') (c : C a b) :
      p ▹D c = transport (λu, C (u.1) (u.2)) (dpair_eq_dpair p idp) c :=
  by cases p; apply idp

  definition sigma_eq_eq_sigma_eq {p1 q1 : a = a'} {p2 : p1 ▹ b = b'} {q2 : q1 ▹ b = b'}
      (r : p1 = q1) (s : r ▹ p2 = q2) : sigma_eq p1 p2 = sigma_eq q1 q2 :=
  by cases r; cases s; apply idp

  /- A path between paths in a total space is commonly shown component wise. -/
  definition sigma_eq2 {p q : u = v} (r : p..1 = q..1) (s : r ▹ p..2 = q..2)
    : p = q :=
  begin
    reverts [q, r, s],
    cases p, cases u with [u1, u2],
    intros [q, r, s],
    apply concat, rotate 1,
    apply sigma_eq_eta,
    apply (sigma_eq_eq_sigma_eq r s)
  end

  /- In Coq they often have to give u and v explicitly when using the following definition -/
  definition sigma_eq2_uncurried {p q : u = v}
      (rs : Σ(r : p..1 = q..1), transport (λx, transport B x u.2 = v.2) r p..2 = q..2) : p = q :=
  destruct rs sigma_eq2

  /- Transport -/

  /- The concrete description of transport in sigmas (and also pis) is rather trickier than in the other types.  In particular, these cannot be described just in terms of transport in simpler types; they require also the dependent transport [transportD].

  In particular, this indicates why `transport` alone cannot be fully defined by induction on the structure of types, although Id-elim/transportD can be (cf. Observational Type Theory).  A more thorough set of lemmas, along the lines of the present ones but dealing with Id-elim rather than just transport, might be nice to have eventually? -/

  definition transport_eq (p : a = a') (bc : Σ(b : B a), C a b)
      : p ▹ bc = ⟨p ▹ bc.1, p ▹D bc.2⟩ :=
  by cases p; cases bc; apply idp

  /- The special case when the second variable doesn't depend on the first is simpler. -/
  definition tr_eq_nondep {B : Type} {C : A → B → Type} (p : a = a') (bc : Σ(b : B), C a b)
      : p ▹ bc = ⟨bc.1, p ▹ bc.2⟩ :=
  by cases p; cases bc; apply idp

  /- Or if the second variable contains a first component that doesn't depend on the first. -/

  definition tr_eq2_nondep {C : A → Type} {D : Π a:A, B a → C a → Type} (p : a = a')
      (bcd : Σ(b : B a) (c : C a), D a b c) : p ▹ bcd = ⟨p ▹ bcd.1, p ▹ bcd.2.1, p ▹D2 bcd.2.2⟩ :=
  begin
    cases p, cases bcd with [b, cd],
    cases cd, apply idp
  end

  /- Functorial action -/
  variables (f : A → A') (g : Πa, B a → B' (f a))

  definition sigma_functor (u : Σa, B a) : Σa', B' a' :=
  ⟨f u.1, g u.1 u.2⟩

  /- Equivalences -/

  definition is_equiv_sigma_functor [H1 : is_equiv f] [H2 : Π a, is_equiv (g a)]
      : is_equiv (sigma_functor f g) :=
  adjointify (sigma_functor f g)
             (sigma_functor f⁻¹ (λ(a' : A') (b' : B' a'),
               ((g (f⁻¹ a'))⁻¹ (transport B' (right_inv f a')⁻¹ b'))))
  begin
    intro u',
    cases u' with [a', b'],
    apply (sigma_eq (right_inv f a')),
  --   rewrite right_inv,
  -- end
    -- "rewrite right_inv (g (f⁻¹ a'))"
    apply concat, apply (ap (λx, (transport B' (right_inv f a') x))), apply (right_inv (g (f⁻¹ a'))),
    show right_inv f a' ▹ ((right_inv f a')⁻¹ ▹ b') = b',
    from tr_inv_tr _ (right_inv f a') b'
  end
  begin
    intro u,
    cases u with [a, b],
    apply (sigma_eq (left_inv f a)),
    show transport B (left_inv f a) ((g (f⁻¹ (f a)))⁻¹ (transport B' (right_inv f (f a))⁻¹ (g a b))) = b,
    from calc
      transport B (left_inv f a) ((g (f⁻¹ (f a)))⁻¹ (transport B' (right_inv f (f a))⁻¹ (g a b)))
          = (g a)⁻¹ (transport (B' ∘ f) (left_inv f a) (transport B' (right_inv f (f a))⁻¹ (g a b)))
              : by rewrite (fn_tr_eq_tr_fn (left_inv f a) (λ a, (g a)⁻¹))
      ... = (g a)⁻¹ (transport B' (ap f (left_inv f a)) (transport B' (right_inv f (f a))⁻¹ (g a b)))
              : ap (g a)⁻¹ !transport_compose
      ... = (g a)⁻¹ (transport B' (ap f (left_inv f a)) (transport B' (ap f (left_inv f a))⁻¹ (g a b)))
           : ap (λ x, (g a)⁻¹ (transport B' (ap f (left_inv f a)) (transport B' x⁻¹ (g a b)))) (adj f a)
      ... = (g a)⁻¹ (g a b) : {!tr_inv_tr}
      ... = b : by rewrite (left_inv (g a) b)
  end

  definition sigma_equiv_sigma_of_is_equiv [H1 : is_equiv f] [H2 : Π a, is_equiv (g a)]
    : (Σa, B a) ≃ (Σa', B' a') :=
  equiv.mk (sigma_functor f g) !is_equiv_sigma_functor

  section
  local attribute inv [irreducible]
  local attribute function.compose [irreducible] --this is needed for the following class inference problem
  definition sigma_equiv_sigma (Hf : A ≃ A') (Hg : Π a, B a ≃ B' (to_fun Hf a)) :
      (Σa, B a) ≃ (Σa', B' a') :=
  sigma_equiv_sigma_of_is_equiv (to_fun Hf) (λ a, to_fun (Hg a))
  end

  definition sigma_equiv_sigma_id {B' : A → Type} (Hg : Π a, B a ≃ B' a) : (Σa, B a) ≃ Σa, B' a :=
  sigma_equiv_sigma equiv.refl Hg

  definition ap_sigma_functor_eq_dpair (p : a = a') (q : p ▹ b = b')
    : ap (sigma.sigma_functor f g) (sigma_eq p q)
    = sigma_eq (ap f p)
                 ((transport_compose _ f p (g a b))⁻¹ ⬝ (fn_tr_eq_tr_fn p g b)⁻¹ ⬝ ap (g a') q) :=
  by cases p; cases q; apply idp

  definition ap_sigma_functor_eq (p : u.1 = v.1) (q : p ▹ u.2 = v.2)
    : ap (sigma.sigma_functor f g) (sigma_eq p q) =
      sigma_eq (ap f p)
       ((transport_compose B' f p (g u.1 u.2))⁻¹ ⬝ (fn_tr_eq_tr_fn p g u.2)⁻¹ ⬝ ap (g v.1) q) :=
  by cases u; cases v; apply ap_sigma_functor_eq_dpair

  /- definition 3.11.9(i): Summing up a contractible family of types does nothing. -/
  open is_trunc
  definition is_equiv_pr1 [instance] (B : A → Type) [H : Π a, is_contr (B a)]
      : is_equiv (@pr1 A B) :=
  adjointify pr1
             (λa, ⟨a, !center⟩)
             (λa, idp)
             (λu, sigma_eq idp !contr)

  definition sigma_equiv_of_is_contr_pr2 [H : Π a, is_contr (B a)] : (Σa, B a) ≃ A :=
  equiv.mk pr1 _

  /- definition 3.11.9(ii): Dually, summing up over a contractible type does nothing. -/

  definition sigma_equiv_of_is_contr_pr1 (B : A → Type) [H : is_contr A] : (Σa, B a) ≃ B (center A)
  :=
  equiv.mk _ (adjointify
    (λu, (contr u.1)⁻¹ ▹ u.2)
    (λb, ⟨!center, b⟩)
    (λb, ap (λx, x ▹ b) !hprop_eq_of_is_contr)
    (λu, sigma_eq !contr !tr_inv_tr))

  /- Associativity -/

  --this proof is harder than in Coq because we don't have eta definitionally for sigma
  definition sigma_assoc_equiv (C : (Σa, B a) → Type) : (Σa b, C ⟨a, b⟩) ≃ (Σu, C u) :=
  equiv.mk _ (adjointify
    (λav, ⟨⟨av.1, av.2.1⟩, av.2.2⟩)
    (λuc, ⟨uc.1.1, uc.1.2, !eta⁻¹ ▹ uc.2⟩)
    begin intro uc; cases uc with [u, c]; cases u; apply idp end
    begin intro av; cases av with [a, v]; cases v; apply idp end)

  open prod
  definition assoc_equiv_prod (C : (A × A') → Type) : (Σa a', C (a,a')) ≃ (Σu, C u) :=
  equiv.mk _ (adjointify
    (λav, ⟨(av.1, av.2.1), av.2.2⟩)
    (λuc, ⟨pr₁ (uc.1), pr₂ (uc.1), !prod.eta⁻¹ ▹ uc.2⟩)
    proof (λuc, destruct uc (λu, prod.destruct u (λa b c, idp))) qed
    proof (λav, destruct av (λa v, destruct v (λb c, idp))) qed)

  /- Symmetry -/

  definition comm_equiv_uncurried (C : A × A' → Type) : (Σa a', C (a, a')) ≃ (Σa' a, C (a, a')) :=
  calc
    (Σa a', C (a, a')) ≃ Σu, C u : assoc_equiv_prod
                 ... ≃ Σv, C (flip v) : sigma_equiv_sigma !prod_comm_equiv
                                          (λu, prod.destruct u (λa a', equiv.refl))
                 ... ≃ (Σa' a, C (a, a')) : assoc_equiv_prod

  definition sigma_comm_equiv (C : A → A' → Type) : (Σa a', C a a') ≃ (Σa' a, C a a') :=
  comm_equiv_uncurried (λu, C (prod.pr1 u) (prod.pr2 u))

  definition equiv_prod (A B : Type) : (Σ(a : A), B) ≃ A × B :=
  equiv.mk _ (adjointify
    (λs, (s.1, s.2))
    (λp, ⟨pr₁ p, pr₂ p⟩)
    proof (λp, prod.destruct p (λa b, idp)) qed
    proof (λs, destruct s (λa b, idp)) qed)

  definition comm_equiv_nondep (A B : Type) : (Σ(a : A), B) ≃ Σ(b : B), A :=
  calc
    (Σ(a : A), B) ≃ A × B       : equiv_prod
              ... ≃ B × A       : prod_comm_equiv
              ... ≃ Σ(b : B), A : equiv_prod

  /- ** Universal mapping properties -/
  /- *** The positive universal property. -/

  section
  definition is_equiv_sigma_rec [instance] (C : (Σa, B a) → Type)
    : is_equiv (sigma.rec : (Πa b, C ⟨a, b⟩) → Πab, C ab) :=
  adjointify _ (λ g a b, g ⟨a, b⟩)
               (λ g, proof eq_of_homotopy (λu, destruct u (λa b, idp)) qed)
               (λ f, refl f)

  definition equiv_sigma_rec (C : (Σa, B a) → Type)
    : (Π(a : A) (b: B a), C ⟨a, b⟩) ≃ (Πxy, C xy) :=
  equiv.mk sigma.rec _

  /- *** The negative universal property. -/

  protected definition coind_uncurried (fg : Σ(f : Πa, B a), Πa, C a (f a)) (a : A)
    : Σ(b : B a), C a b :=
  ⟨fg.1 a, fg.2 a⟩

  protected definition coind (f : Π a, B a) (g : Π a, C a (f a)) (a : A) : Σ(b : B a), C a b :=
  coind_uncurried ⟨f, g⟩ a

  --is the instance below dangerous?
  --in Coq this can be done without function extensionality
  definition is_equiv_coind [instance] (C : Πa, B a → Type)
    : is_equiv (@coind_uncurried _ _ C) :=
  adjointify _ (λ h, ⟨λa, (h a).1, λa, (h a).2⟩)
               (λ h, proof eq_of_homotopy (λu, !eta) qed)
               (λfg, destruct fg (λ(f : Π (a : A), B a) (g : Π (x : A), C x (f x)), proof idp qed))

  definition sigma_pi_equiv_pi_sigma : (Σ(f : Πa, B a), Πa, C a (f a)) ≃ (Πa, Σb, C a b) :=
  equiv.mk coind_uncurried _
  end

  /- ** Subtypes (sigma types whose second components are hprops) -/

  /- To prove equality in a subtype, we only need equality of the first component. -/
  definition subtype_eq [H : Πa, is_hprop (B a)] (u v : Σa, B a) : u.1 = v.1 → u = v :=
  (sigma_eq_uncurried ∘ (@inv _ _ pr1 (@is_equiv_pr1 _ _ (λp, !is_trunc.is_trunc_eq))))

  definition is_equiv_subtype_eq [H : Πa, is_hprop (B a)] (u v : Σa, B a)
      : is_equiv (subtype_eq u v) :=
  !is_equiv_compose
  local attribute is_equiv_subtype_eq [instance]

  definition equiv_subtype [H : Πa, is_hprop (B a)] (u v : Σa, B a) : (u.1 = v.1) ≃ (u = v) :=
  equiv.mk !subtype_eq _

  /- truncatedness -/
  definition is_trunc_sigma (B : A → Type) (n : trunc_index)
      [HA : is_trunc n A] [HB : Πa, is_trunc n (B a)] : is_trunc n (Σa, B a) :=
  begin
  reverts [A, B, HA, HB],
  apply (trunc_index.rec_on n),
    intros [A, B, HA, HB],
      fapply is_trunc.is_trunc_equiv_closed,
        apply equiv.symm,
          apply sigma_equiv_of_is_contr_pr1,
     intros [n, IH, A, B, HA, HB],
       fapply is_trunc.is_trunc_succ_intro, intros [u, v],
      fapply is_trunc.is_trunc_equiv_closed,
         apply equiv_sigma_eq,
         apply IH,
           apply is_trunc.is_trunc_eq,
           intro p,
             show is_trunc n (p ▹ u .2 = v .2), from
             is_trunc.is_trunc_eq n (p ▹ u.2) (v.2),
  end

end sigma

attribute sigma.is_trunc_sigma [instance] [priority 1505]

open is_trunc sigma prod
/- truncatedness -/
definition prod.is_trunc_prod [instance] [priority 1490] (A B : Type) (n : trunc_index)
  [HA : is_trunc n A] [HB : is_trunc n B] : is_trunc n (A × B) :=
is_trunc.is_trunc_equiv_closed n !equiv_prod
