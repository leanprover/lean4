/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn
Ported from Coq HoTT

Theorems about sigma-types (dependent sums)
-/

import ..trunc .prod
open path sigma sigma.ops equiv is_equiv

namespace sigma
  -- remove the ₁'s (globally)
  variables {A A' : Type} {B : A → Type} {B' : A' → Type} {C : Πa, B a → Type}
            {D : Πa b, C a b → Type}
            {a a' a'' : A} {b b₁ b₂ : B a} {b' : B a'} {b'' : B a''} {u v w : Σa, B a}

  definition eta_sigma (u : Σa, B a) : ⟨u.1 , u.2⟩ ≈ u :=
  destruct u (λu1 u2, idp)

  definition eta2_sigma (u : Σa b, C a b) : ⟨u.1, u.2.1, u.2.2⟩ ≈ u :=
  destruct u (λu1 u2, destruct u2 (λu21 u22, idp))

  definition eta3_sigma (u : Σa b c, D a b c) : ⟨u.1, u.2.1, u.2.2.1, u.2.2.2⟩ ≈ u :=
  destruct u (λu1 u2, destruct u2 (λu21 u22, destruct u22 (λu221 u222, idp)))

  definition path_sigma_dpair (p : a ≈ a') (q : p ▹ b ≈ b') : dpair a b ≈ dpair a' b' :=
  path.rec_on p (λb b' q, path.rec_on q idp) b b' q

  /- In Coq they often have to give u and v explicitly -/
  definition path_sigma (p : u.1 ≈ v.1) (q : p ▹ u.2 ≈ v.2) : u ≈ v :=
  destruct u
           (λu1 u2, destruct v (λ v1 v2, path_sigma_dpair))
           p q

  /- Projections of paths from a total space -/

  definition pr1_path (p : u ≈ v) : u.1 ≈ v.1 :=
  ap dpr1 p

  postfix `..1`:(max+1) := pr1_path

  definition pr2_path (p : u ≈ v) : p..1 ▹ u.2 ≈ v.2 :=
  path.rec_on p idp
  --Coq uses the following proof, which only computes if u,v are dpairs AND p is idp
  --(transport_compose B dpr1 p u.2)⁻¹ ⬝ apD dpr2 p

  postfix `..2`:(max+1) := pr2_path

  definition dpair_path_sigma (p : u.1 ≈ v.1) (q : p ▹ u.2 ≈ v.2)
      :  dpair (path_sigma p q)..1 (path_sigma p q)..2 ≈ ⟨p, q⟩ :=
  begin
    generalize q, generalize p,
    apply (destruct u), intros (u1, u2),
    apply (destruct v), intros (v1, v2, p), generalize v2,
    apply (path.rec_on p), intros (v2, q),
    apply (path.rec_on q), apply idp
  end

  definition pr1_path_sigma (p : u.1 ≈ v.1) (q : p ▹ u.2 ≈ v.2) : (path_sigma p q)..1 ≈ p :=
  (!dpair_path_sigma)..1

  definition pr2_path_sigma (p : u.1 ≈ v.1) (q : p ▹ u.2 ≈ v.2)
      : pr1_path_sigma p q ▹ (path_sigma p q)..2 ≈ q :=
  (!dpair_path_sigma)..2

  definition eta_path_sigma (p : u ≈ v) : path_sigma (p..1) (p..2) ≈ p :=
  begin
    apply (path.rec_on p),
    apply (destruct u), intros (u1, u2),
    apply idp
  end

  definition transport_pr1_path_sigma {B' : A → Type} (p : u.1 ≈ v.1) (q : p ▹ u.2 ≈ v.2)
      : transport (λx, B' x.1) (path_sigma p q) ≈ transport B' p :=
  begin
    generalize q, generalize p,
    apply (destruct u), intros (u1, u2),
    apply (destruct v), intros (v1, v2, p), generalize v2,
    apply (path.rec_on p), intros (v2, q),
    apply (path.rec_on q), apply idp
  end

  /- the uncurried version of path_sigma. We will prove that this is an equivalence -/

  definition path_sigma_uncurried (pq : Σ(p : dpr1 u ≈ dpr1 v), p ▹ (dpr2 u) ≈ dpr2 v) : u ≈ v :=
  destruct pq path_sigma

  definition dpair_path_sigma_uncurried (pq : Σ(p : u.1 ≈ v.1), p ▹ u.2 ≈ v.2)
      :  dpair (path_sigma_uncurried pq)..1 (path_sigma_uncurried pq)..2 ≈ pq :=
  destruct pq dpair_path_sigma

  definition pr1_path_sigma_uncurried (pq : Σ(p : u.1 ≈ v.1), p ▹ u.2 ≈ v.2)
      : (path_sigma_uncurried pq)..1 ≈ pq.1 :=
  (!dpair_path_sigma_uncurried)..1

  definition pr2_path_sigma_uncurried (pq : Σ(p : u.1 ≈ v.1), p ▹ u.2 ≈ v.2)
      : (pr1_path_sigma_uncurried pq) ▹ (path_sigma_uncurried pq)..2 ≈ pq.2 :=
  (!dpair_path_sigma_uncurried)..2

  definition eta_path_sigma_uncurried (p : u ≈ v) : path_sigma_uncurried (dpair p..1 p..2) ≈ p :=
  !eta_path_sigma

  definition transport_pr1_path_sigma_uncurried {B' : A → Type} (pq : Σ(p : u.1 ≈ v.1), p ▹ u.2 ≈ v.2)
      : transport (λx, B' x.1) (@path_sigma_uncurried A B u v pq) ≈ transport B' pq.1 :=
    destruct pq transport_pr1_path_sigma

  definition isequiv_path_sigma /-[instance]-/ (u v : Σa, B a)
      : is_equiv (@path_sigma_uncurried A B u v) :=
  adjointify path_sigma_uncurried
             (λp, ⟨p..1, p..2⟩)
             eta_path_sigma_uncurried
             dpair_path_sigma_uncurried

  definition equiv_path_sigma (u v : Σa, B a) : (Σ(p : u.1 ≈ v.1),  p ▹ u.2 ≈ v.2) ≃ (u ≈ v) :=
    equiv.mk path_sigma_uncurried !isequiv_path_sigma

  definition path_sigma_dpair_pp_pp (p1 : a  ≈ a' ) (q1 : p1 ▹ b  ≈ b' )
                                    (p2 : a' ≈ a'') (q2 : p2 ▹ b' ≈ b'') :
      path_sigma_dpair (p1 ⬝ p2) (transport_pp B p1 p2 b ⬝ ap (transport B p2) q1 ⬝ q2)
    ≈ path_sigma_dpair p1 q1 ⬝ path_sigma_dpair  p2 q2 :=
  begin
    generalize q2, generalize q1, generalize b'', generalize p2, generalize b',
    apply (path.rec_on p1), intros (b', p2),
    apply (path.rec_on p2), intros (b'', q1),
    apply (path.rec_on q1), intro q2,
    apply (path.rec_on q2), apply idp
  end

  definition path_sigma_pp_pp (p1 : u.1 ≈ v.1) (q1 : p1 ▹ u.2 ≈ v.2)
                              (p2 : v.1 ≈ w.1) (q2 : p2 ▹ v.2 ≈ w.2) :
      path_sigma (p1 ⬝ p2) (transport_pp B p1 p2 u.2 ⬝ ap (transport B p2) q1 ⬝ q2)
    ≈ path_sigma p1 q1 ⬝ path_sigma p2 q2 :=
  begin
    generalize q2, generalize p2, generalize q1, generalize p1,
    apply (destruct u), intros (u1, u2),
    apply (destruct v), intros (v1, v2),
    apply (destruct w), intros,
    apply path_sigma_dpair_pp_pp
  end

  definition path_sigma_dpair_p1_1p (p : a ≈ a') (q : p ▹ b ≈ b') :
      path_sigma_dpair p q ≈ path_sigma_dpair p idp ⬝ path_sigma_dpair idp q :=
  begin
    generalize q, generalize b',
    apply (path.rec_on p), intros (b', q),
    apply (path.rec_on q), apply idp
  end

  /- pr1_path commutes with the groupoid structure. -/

  definition pr1_path_1  (u : Σa, B a)           : (idpath u)..1 ≈ idpath (u.1)    := idp
  definition pr1_path_pp (p : u ≈ v) (q : v ≈ w) : (p ⬝ q)   ..1 ≈ (p..1) ⬝ (q..1) := !ap_pp
  definition pr1_path_V  (p : u ≈ v)             : p⁻¹       ..1 ≈ (p..1)⁻¹        := !ap_V

  /- Applying dpair to one argument is the same as path_sigma_dpair with reflexivity in the first place. -/

  definition ap_dpair (q : b₁ ≈ b₂) : ap (dpair a) q ≈ path_sigma_dpair idp q :=
  path.rec_on q idp

  /- Dependent transport is the same as transport along a path_sigma. -/

  definition transportD_is_transport (p : a ≈ a') (c : C a b) :
      p ▹D c ≈ transport (λu, C (u.1) (u.2)) (path_sigma_dpair p idp) c :=
  path.rec_on p idp

  definition path_path_sigma_path_sigma {p1 q1 : a ≈ a'} {p2 : p1 ▹ b ≈ b'} {q2 : q1 ▹ b ≈ b'}
      (r : p1 ≈ q1) (s : r ▹ p2 ≈ q2) : path_sigma p1 p2 ≈ path_sigma q1 q2 :=
  path.rec_on r
              proof (λq2 s, path.rec_on s idp) qed
              q2
              s
  -- begin
  --   generalize s, generalize q2,
  --   apply (path.rec_on r), intros (q2, s),
  --   apply (path.rec_on s), apply idp
  -- end


  /- A path between paths in a total space is commonly shown component wise. -/
  definition path_path_sigma {p q : u ≈ v} (r : p..1 ≈ q..1) (s : r ▹ p..2 ≈ q..2) : p ≈ q :=
  begin
    generalize s, generalize r, generalize q,
    apply (path.rec_on p),
    apply (destruct u), intros (u1, u2, q, r, s),
    apply concat, rotate 1,
    apply eta_path_sigma,
    apply (path_path_sigma_path_sigma r s)
  end


  /- In Coq they often have to give u and v explicitly when using the following definition -/
  definition path_path_sigma_uncurried {p q : u ≈ v}
      (rs : Σ(r : p..1 ≈ q..1), transport (λx, transport B x u.2 ≈ v.2) r p..2 ≈ q..2) : p ≈ q :=
  destruct rs path_path_sigma

  /- Transport -/

  /- The concrete description of transport in sigmas (and also pis) is rather trickier than in the other types.  In particular, these cannot be described just in terms of transport in simpler types; they require also the dependent transport [transportD].

  In particular, this indicates why `transport` alone cannot be fully defined by induction on the structure of types, although Id-elim/transportD can be (cf. Observational Type Theory).  A more thorough set of lemmas, along the lines of the present ones but dealing with Id-elim rather than just transport, might be nice to have eventually? -/

  definition transport_sigma (p : a ≈ a') (bc : Σ(b : B a), C a b) : p ▹ bc ≈ ⟨p ▹ bc.1, p ▹D bc.2⟩
  :=
  begin
    apply (path.rec_on p),
    apply (destruct bc), intros (b, c),
    apply idp
  end

  /- The special case when the second variable doesn't depend on the first is simpler. -/
  definition transport_sigma' {B : Type} {C : A → B → Type} (p : a ≈ a') (bc : Σ(b : B), C a b)
      : p ▹ bc ≈ ⟨bc.1, p ▹ bc.2⟩ :=
  begin
    apply (path.rec_on p),
    apply (destruct bc), intros (b, c),
    apply idp
  end

  /- Or if the second variable contains a first component that doesn't depend on the first.  Need to think about the naming of these. -/

  definition transport_sigma_' {C : A → Type} {D : Π a:A, B a → C a → Type} (p : a ≈ a')
      (bcd : Σ(b : B a) (c : C a), D a b c) : p ▹ bcd ≈ ⟨p ▹ bcd.1, p ▹ bcd.2.1, p ▹D2 bcd.2.2⟩ :=
  begin
    generalize bcd,
    apply (path.rec_on p), intro bcd,
    apply (destruct bcd), intros (b, cd),
    apply (destruct cd), intros (c, d),
    apply idp
  end

  /- Functorial action -/
  variables (f : A → A') (g : Πa, B a → B' (f a))

  definition functor_sigma (u : Σa, B a) : Σa', B' a' :=
  ⟨f u.1, g u.1 u.2⟩

  /- Equivalences -/

  --remove explicit arguments of IsEquiv
  definition isequiv_functor_sigma [H1 : is_equiv f] [H2 : Π a, @is_equiv (B a) (B' (f a)) (g a)]
      : is_equiv (functor_sigma f g) :=
  /-adjointify (functor_sigma f g)
             (functor_sigma (f⁻¹) (λ(x : A') (y : B' x), ((g (f⁻¹ x))⁻¹ ((retr f x)⁻¹ ▹ y))))
             sorry-/
             sorry

  definition equiv_functor_sigma [H1 : is_equiv f] [H2 : Π a, is_equiv (g a)] : (Σa, B a) ≃ (Σa', B' a') :=
  equiv.mk (functor_sigma f g) !isequiv_functor_sigma

  context --remove
  irreducible inv function.compose --remove
  definition equiv_functor_sigma' (Hf : A ≃ A') (Hg : Π a, B a ≃ B' (to_fun Hf a)) :
      (Σa, B a) ≃ (Σa', B' a') :=
  equiv_functor_sigma (to_fun Hf) (λ a, to_fun (Hg a))
  end --remove

  /- definition 3.11.9(i): Summing up a contractible family of types does nothing. -/
  open truncation
  definition isequiv_pr1_contr [instance] (B : A → Type) [H : Π a, is_contr (B a)]
      : is_equiv (@dpr1 A B) :=
  adjointify dpr1
             (λa, ⟨a, !center⟩)
             (λa, idp)
             (λu, path_sigma idp !contr)

  definition equiv_sigma_contr [H : Π a, is_contr (B a)] : (Σa, B a) ≃ A :=
  equiv.mk dpr1 _

  /- definition 3.11.9(ii): Dually, summing up over a contractible type does nothing. -/

  definition equiv_contr_sigma (B : A → Type) [H : is_contr A] : (Σa, B a) ≃ B (center A) :=
  equiv.mk _ (adjointify
    (λu, contr u.1⁻¹ ▹ u.2)
    (λb, ⟨!center, b⟩)
    (λb, ap (λx, x ▹ b) !path2_contr)
    (λu, path_sigma !contr !transport_pV))

  /- Associativity -/

  --this proof is harder here than in Coq because we don't have eta definitionally for sigma
  definition equiv_sigma_assoc (C : (Σa, B a) → Type) : (Σa b, C ⟨a,b⟩) ≃ (Σu, C u) :=
  -- begin
  --   apply Equiv.mk,
  --   apply (adjointify (λav, ⟨⟨av.1, av.2.1⟩, av.2.2⟩)
  --                     (λuc, ⟨uc.1.1, uc.1.2, !eta_sigma⁻¹ ▹ uc.2⟩)),
  --     intro uc, apply (destruct uc), intro u,
  --               apply (destruct u), intros (a, b, c),
  --               apply idp,
  --     intro av, apply (destruct av), intros (a, v),
  --               apply (destruct v), intros (b, c),
  --               apply idp,
  -- end
  equiv.mk _ (adjointify
    (λav, ⟨⟨av.1, av.2.1⟩, av.2.2⟩)
    (λuc, ⟨uc.1.1, uc.1.2, !eta_sigma⁻¹ ▹ uc.2⟩)
    proof (λuc, destruct uc (λu, destruct u (λa b c, idp))) qed
    proof (λav, destruct av (λa v, destruct v (λb c, idp))) qed)

  open prod
  definition equiv_sigma_prod (C : (A × A') → Type) : (Σa a', C (a,a')) ≃ (Σu, C u) :=
  equiv.mk _ (adjointify
    (λav, ⟨(av.1, av.2.1), av.2.2⟩)
    (λuc, ⟨pr₁ (uc.1), pr₂ (uc.1), !eta_prod⁻¹ ▹ uc.2⟩)
    proof (λuc, destruct uc (λu, prod.destruct u (λa b c, idp))) qed
    proof (λav, destruct av (λa v, destruct v (λb c, idp))) qed)


  /- Symmetry -/
  -- if this breaks, replace "Equiv.id" by "proof Equiv.id qed"
  definition equiv_sigma_symm_prod (C : A × A' → Type) : (Σa a', C (a, a')) ≃ (Σa' a, C (a, a')) :=
  calc
    (Σa a', C (a, a')) ≃ Σu, C u : equiv_sigma_prod
                 ... ≃ Σv, C (flip v) : equiv_functor_sigma' !equiv_prod_symm
                                          (λu, prod.destruct u (λa a', equiv.refl))
                 ... ≃ (Σa' a, C (a, a')) : equiv_sigma_prod

  definition equiv_sigma_symm (C : A → A' → Type) : (Σa a', C a a') ≃ (Σa' a, C a a') :=
  sigma.equiv_sigma_symm_prod (λu, C (pr1 u) (pr2 u))

  definition equiv_sigma0_prod (A B : Type) : (Σ(a : A), B) ≃ A × B :=
  equiv.mk _ (adjointify
    (λs, (s.1, s.2))
    (λp, ⟨pr₁ p, pr₂ p⟩)
    proof (λp, prod.destruct p (λa b, idp)) qed
    proof (λs, destruct s (λa b, idp)) qed)

  definition equiv_sigma_symm0 (A B : Type) : (Σ(a : A), B) ≃ Σ(b : B), A :=
  calc
    (Σ(a : A), B) ≃ A × B : equiv_sigma0_prod
              ... ≃ B × A : equiv_prod_symm
              ... ≃ Σ(b : B), A : equiv_sigma0_prod

  /- truncatedness -/
  definition trunc_sigma [instance] (B : A → Type) (n : trunc_index)
      [HA : is_trunc n A] [HB : Πa, is_trunc n (B a)] : is_trunc n (Σa, B a) :=
begin
  reverts (A, B, HA, HB),
  apply (truncation.trunc_index.rec_on n),
    intros (A, B, HA, HB),
      fapply trunc_equiv',
        apply equiv.symm,
          apply equiv_contr_sigma, apply HA, --should be solved by term synthesis
        apply HB,
     intros (n, IH, A, B, HA, HB),
       fapply is_trunc_succ, intros (u, v),
      fapply trunc_equiv',
         apply equiv_path_sigma,
         apply IH,
           apply (succ_is_trunc n),
           intro p,
             show is_trunc n (p ▹ u .2 ≈ v .2), from
             succ_is_trunc n (p ▹ u.2) (v.2),
end

end sigma
