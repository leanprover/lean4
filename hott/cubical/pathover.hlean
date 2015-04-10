/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: types.pathover
Author: Floris van Doorn

Theorems about pathovers
-/

import .sigma arity

open eq equiv is_equiv equiv.ops

namespace cubical

  variables {A A' : Type} {B : A → Type} {C : Πa, B a → Type}
            {a a₂ a₃ a₄ : A} {p : a = a₂} {p₂ : a₂ = a₃} {p₃ : a₃ = a₄}
            {b : B a} {b₂ : B a₂} {b₃ : B a₃} {b₄ : B a₄}
            {c : C a b} {c₂ : C a₂ b₂}
            {u v w : Σa, B a}

  inductive pathover (B : A → Type) (b : B a) : Π{a₂ : A} (p : a = a₂) (b₂ : B a₂), Type :=
  idpatho : pathover B b (refl a) b

  notation b `=[`:50 p:0 `]`:0 b₂:50 := pathover _ b p b₂

  definition idpo [reducible] {b : B a} : b =[refl a] b :=
  pathover.idpatho b

  /- equivalences with equality using transport -/
  definition pathover_of_transport_eq (r : p ▹ b = b₂) : b =[p] b₂ :=
  by cases p; cases r; exact idpo

  definition pathover_of_eq_transport (r : b = p⁻¹ ▹ b₂) : b =[p] b₂ :=
  by cases p; cases r; exact idpo

  definition transport_eq_of_pathover (r : b =[p] b₂) : p ▹ b = b₂ :=
  by cases r; exact idp

  definition eq_transport_of_pathover (r : b =[p] b₂) : b = p⁻¹ ▹ b₂ :=
  by cases r; exact idp

  definition pathover_equiv_transport_eq (p : a = a₂) (b : B a) (b₂ : B a₂)
    : (b =[p] b₂) ≃ (p ▹ b = b₂) :=
  begin
    fapply equiv.MK,
    { exact transport_eq_of_pathover},
    { exact pathover_of_transport_eq},
    { intro r, cases p, cases r, apply idp},
    { intro r, cases r, apply idp},
  end

  definition pathover_equiv_eq_transport (p : a = a₂) (b : B a) (b₂ : B a₂)
    : (b =[p] b₂) ≃ (b = p⁻¹ ▹ b₂) :=
  begin
    fapply equiv.MK,
    { exact eq_transport_of_pathover},
    { exact pathover_of_eq_transport},
    { intro r, cases p, cases r, apply idp},
    { intro r, cases r, apply idp},
  end

  definition pathover_transport (p : a = a₂) (b : B a) : b =[p] p ▹ b :=
  pathover_of_transport_eq idp

  definition transport_pathover (p : a = a₂) (b : B a) : p⁻¹ ▹ b =[p] b :=
  pathover_of_eq_transport idp

  definition concato (r : b =[p] b₂) (r₂ : b₂ =[p₂] b₃) : b =[p ⬝ p₂] b₃ :=
  pathover.rec_on r₂ (pathover.rec_on r idpo)

  definition inverseo (r : b =[p] b₂) : b₂ =[p⁻¹] b :=
  pathover.rec_on r idpo

  definition apdo (f : Πa, B a) (p : a = a₂) : f a =[p] f a₂ :=
  eq.rec_on p idpo

  infix `⬝o`:75 := concato
  postfix `⁻¹ᵒ`:(max+10) := inverseo

  /- Some of the theorems analogous to theorems for = in init.path -/

  definition cono_idpo (r : b =[p] b₂) : r ⬝o idpo =[con_idp p] r :=
  pathover.rec_on r idpo

  definition idpo_cono (r : b =[p] b₂) : idpo ⬝o r =[idp_con p] r :=
  pathover.rec_on r idpo

  definition cono.assoc' (r : b =[p] b₂) (r₂ : b₂ =[p₂] b₃) (r₃ : b₃ =[p₃] b₄) :
    r ⬝o (r₂ ⬝o r₃) =[!con.assoc'] (r ⬝o r₂) ⬝o r₃ :=
  pathover.rec_on r₃ (pathover.rec_on r₂ (pathover.rec_on r idpo))

  definition cono.assoc (r : b =[p] b₂) (r₂ : b₂ =[p₂] b₃) (r₃ : b₃ =[p₃] b₄) :
    (r ⬝o r₂) ⬝o r₃ =[!con.assoc] r ⬝o (r₂ ⬝o r₃) :=
  pathover.rec_on r₃ (pathover.rec_on r₂ (pathover.rec_on r idpo))

  -- the left inverse law.
  definition cono.right_inv (r : b =[p] b₂) : r ⬝o r⁻¹ᵒ =[!con.right_inv] idpo :=
  pathover.rec_on r idpo

  -- the right inverse law.
  definition cono.left_inv (r : b =[p] b₂) : r⁻¹ᵒ ⬝o r =[!con.left_inv] idpo :=
  pathover.rec_on r idpo

  /- Some of the theorems analogous to theorems for transport in init.path -/
  --set_option pp.notation false
  definition pathover_constant (p : a = a₂) (a' a₂' : A') : a' =[p] a₂' ≃ a' = a₂' :=
  begin
    fapply equiv.MK,
    { intro r, cases r, exact idp},
    { intro r, cases p, cases r, exact idpo},
    { intro r, cases p, cases r, exact idp},
    { intro r, cases r, exact idp},
  end

  definition pathover_idp (b : B a) (b' : B a) : b =[idpath a] b' ≃ b = b' :=
  pathover_equiv_transport_eq idp b b'

  definition eq_of_pathover_idp {b' : B a} (q : b =[idpath a] b') : b = b' :=
  transport_eq_of_pathover q

  definition pathover_idp_of_eq {b' : B a} (q : b = b') : b =[idpath a] b' :=
  pathover_of_transport_eq q

  definition idp_rec_on {P : Π⦃b₂ : B a⦄, b =[idpath a] b₂ → Type}
    {b₂ : B a} (r : b =[idpath a] b₂) (H : P idpo) : P r :=
  have H2 : P (pathover_idp_of_eq (eq_of_pathover_idp r)),
    from eq.rec_on (eq_of_pathover_idp r) H,
  left_inv !pathover_idp r ▹ H2

  --pathover with fibration B' ∘ f
  definition pathover_compose (B' : A' → Type) (f : A → A') (p : a = a₂)
    (b : B' (f a)) (b₂ : B' (f a₂)) : b =[p] b₂ ≃ b =[ap f p] b₂ :=
  begin
    fapply equiv.MK,
    { intro r, cases r, exact idpo},
    { intro r, cases p, apply (idp_rec_on r), apply idpo},
    { intro r, cases p, esimp [function.compose,function.id], apply (idp_rec_on r), apply idp},
    { intro r, cases r, exact idp},
  end

  definition apdo_con (f : Πa, B a) (p : a = a₂) (q : a₂ = a₃)
    : apdo f (p ⬝ q) = apdo f p ⬝o apdo f q :=
  by cases p; cases q; exact idp

  open sigma sigma.ops
  namespace sigma
    /- pathovers used for sigma types -/
    definition dpair_eq_dpair (p : a = a₂) (q : b =[p] b₂) : ⟨a, b⟩ = ⟨a₂, b₂⟩ :=
    by cases q; apply idp

    definition sigma_eq (p : u.1 = v.1) (q : u.2 =[p] v.2) : u = v :=
    by cases u; cases v; apply (dpair_eq_dpair p q)

    /- Projections of paths from a total space -/

    definition pathover_pr2 (p : u = v) : u.2 =[p..1] v.2 :=
    by cases p; apply idpo

    postfix `..2o`:(max+1) := pathover_pr2
    --superfluous notation, but useful if you want an 'o' on both projections
    postfix [parsing-only] `..1o`:(max+1) := eq_pr1

    private definition dpair_sigma_eq (p : u.1 = v.1) (q : u.2 =[p] v.2)
        : ⟨(sigma_eq p q)..1, (sigma_eq p q)..2o⟩ = ⟨p, q⟩ :=
    by cases u; cases v; cases q; apply idp

    definition sigma_eq_pr1 (p : u.1 = v.1) (q : u.2 =[p] v.2) : (sigma_eq p q)..1 = p :=
    (dpair_sigma_eq p q)..1

    definition sigma_eq_pr2 (p : u.1 = v.1) (q : u.2 =[p] v.2)
        : (sigma_eq p q)..2o =[sigma_eq_pr1 p q] q :=
    (dpair_sigma_eq p q)..2o

    definition sigma_eq_eta (p : u = v) : sigma_eq (p..1) (p..2o) = p :=
    by cases p; cases u; apply idp

    /- the uncurried version of sigma_eq. We will prove that this is an equivalence -/

    definition sigma_eq_uncurried : Π (pq : Σ(p : u.1 = v.1), u.2 =[p] v.2), u = v
    | sigma_eq_uncurried ⟨pq₁, pq₂⟩ := sigma_eq pq₁ pq₂

    definition dpair_sigma_eq_uncurried : Π (pq : Σ(p : u.1 = v.1), u.2 =[p] v.2),
          ⟨(sigma_eq_uncurried pq)..1, (sigma_eq_uncurried pq)..2o⟩ = pq
    | dpair_sigma_eq_uncurried ⟨pq₁, pq₂⟩ := dpair_sigma_eq pq₁ pq₂

    definition sigma_eq_pr1_uncurried (pq : Σ(p : u.1 = v.1), u.2 =[p] v.2)
        : (sigma_eq_uncurried pq)..1 = pq.1 :=
    (dpair_sigma_eq_uncurried pq)..1

    definition sigma_eq_pr2_uncurried (pq : Σ(p : u.1 = v.1), u.2 =[p] v.2)
        : (sigma_eq_uncurried pq)..2o =[sigma_eq_pr1_uncurried pq] pq.2 :=
    (dpair_sigma_eq_uncurried pq)..2o

    definition sigma_eq_eta_uncurried (p : u = v) : sigma_eq_uncurried (sigma.mk p..1 p..2o) = p :=
    sigma_eq_eta p

    definition is_equiv_sigma_eq [instance] (u v : Σa, B a)
        : is_equiv (@sigma_eq_uncurried A B u v) :=
    adjointify sigma_eq_uncurried
               (λp, ⟨p..1, p..2o⟩)
               sigma_eq_eta_uncurried
               dpair_sigma_eq_uncurried

    definition equiv_sigma_eq (u v : Σa, B a) : (Σ(p : u.1 = v.1), u.2 =[p] v.2) ≃ (u = v) :=
    equiv.mk sigma_eq_uncurried !is_equiv_sigma_eq

  end sigma

  definition apD011o (f : Πa, B a → A') (Ha : a = a₂) (Hb : b =[Ha] b₂)
      : f a b = f a₂ b₂ :=
  by cases Hb; exact idp

  definition apD0111o (f : Πa b, C a b → A') (Ha : a = a₂) (Hb : b =[Ha] b₂)
    (Hc : c =[apD011o C Ha Hb] c₂) : f a b c = f a₂ b₂ c₂ :=
  by cases Hb; apply (idp_rec_on Hc); apply idp

  namespace pi
    --the most 'natural' version here needs a notion of "path over a pathover"
    definition pi_pathover {f : Πb, C a b} {g : Πb₂, C a₂ b₂}
      (r : Π(b : B a) (b₂ : B a₂) (q : b =[p] b₂), f b =[apD011o C p q] g b₂) : f =[p] g :=
    begin
      cases p, apply pathover_idp_of_eq,
      apply eq_of_homotopy, intro b,
      apply eq_of_pathover_idp, apply r
    end

    definition pi_pathover' {C : (Σa, B a) → Type} {f : Πb, C ⟨a, b⟩} {g : Πb₂, C ⟨a₂, b₂⟩}
      (r : Π(b : B a) (b₂ : B a₂) (q : b =[p] b₂), f b =[sigma.dpair_eq_dpair p q] g b₂)
      : f =[p] g :=
    begin
      cases p, apply pathover_idp_of_eq,
      apply eq_of_homotopy, intro b,
      apply (@eq_of_pathover_idp _ C), exact (r b b (pathover.idpatho b)),
    end

    definition ap11o {f : Πb, C a b} {g : Πb₂, C a₂ b₂} (r : f =[p] g)
      {b : B a} {b₂ : B a₂} (q : b =[p] b₂) : f b =[apD011o C p q] g b₂ :=
    by cases r; apply (idp_rec_on q); exact idpo

    definition ap10o {f : Πb, C a b} {g : Πb₂, C a₂ b₂} (r : f =[p] g)
      {b : B a} : f b =[apD011o C p !pathover_transport] g (p ▹ b) :=
    by cases r; exact idpo

    -- definition equiv_pi_pathover' (f : Πb, C a b) (g : Πb₂, C a₂ b₂) :
    --   (f =[p] g) ≃ (Π(b : B a), f b =[apD011o C p !pathover_transport] g (p ▹ b)) :=
    -- begin
    --   fapply equiv.MK,
    --   { exact ap10o},
    --   { exact pi_pathover'},
    --   { cases p, exact sorry},
    --   { intro r, cases r, },
    -- end


    -- definition equiv_pi_pathover (f : Πb, C a b) (g : Πb₂, C a₂ b₂) :
    --   (f =[p] g) ≃ (Π(b : B a) (b₂ : B a₂) (q : b =[p] b₂), f b =[apD011o C p q] g b₂) :=
    -- begin
    --   fapply equiv.MK,
    --   { exact ap11o},
    --   { exact pi_pathover},
    --   { cases p, exact sorry},
    --   { intro r, cases r, },
    -- end

  end pi


end cubical
