/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Basic theorems about pathovers
-/

prelude
import .path .equiv

open equiv is_equiv equiv.ops

variables {A A' : Type} {B : A → Type} {C : Πa, B a → Type}
          {a a₂ a₃ a₄ : A} {p p' : a = a₂} {p₂ : a₂ = a₃} {p₃ : a₃ = a₄}
          {b b' : B a} {b₂ b₂' : B a₂} {b₃ : B a₃} {b₄ : B a₄}
          {c : C a b} {c₂ : C a₂ b₂}

namespace eq
  inductive pathover.{l} (B : A → Type.{l}) (b : B a) : Π{a₂ : A}, a = a₂ → B a₂ → Type.{l} :=
  idpatho : pathover B b (refl a) b

  notation b `=[`:50 p:0 `]`:0 b₂:50 := pathover _ b p b₂

  definition idpo [reducible] [constructor] : b =[refl a] b :=
  pathover.idpatho b

  /- equivalences with equality using transport -/
  definition pathover_of_tr_eq (r : p ▸ b = b₂) : b =[p] b₂ :=
  by cases p; cases r; exact idpo

  definition pathover_of_eq_tr (r : b = p⁻¹ ▸ b₂) : b =[p] b₂ :=
  by cases p; cases r; exact idpo

  definition tr_eq_of_pathover [unfold 8] (r : b =[p] b₂) : p ▸ b = b₂ :=
  by cases r; exact idp

  definition eq_tr_of_pathover [unfold 8] (r : b =[p] b₂) : b = p⁻¹ ▸ b₂ :=
  by cases r; exact idp

  definition pathover_equiv_tr_eq [constructor] (p : a = a₂) (b : B a) (b₂ : B a₂)
    : (b =[p] b₂) ≃ (p ▸ b = b₂) :=
  begin
    fapply equiv.MK,
    { exact tr_eq_of_pathover},
    { exact pathover_of_tr_eq},
    { intro r, cases p, cases r, apply idp},
    { intro r, cases r, apply idp},
  end

  definition pathover_equiv_eq_tr [constructor] (p : a = a₂) (b : B a) (b₂ : B a₂)
    : (b =[p] b₂) ≃ (b = p⁻¹ ▸ b₂) :=
  begin
    fapply equiv.MK,
    { exact eq_tr_of_pathover},
    { exact pathover_of_eq_tr},
    { intro r, cases p, cases r, apply idp},
    { intro r, cases r, apply idp},
  end

  definition pathover_tr [unfold 5] (p : a = a₂) (b : B a) : b =[p] p ▸ b :=
  by cases p;exact idpo

  definition tr_pathover [unfold 5] (p : a = a₂) (b : B a₂) : p⁻¹ ▸ b =[p] b :=
  pathover_of_eq_tr idp

  definition concato [unfold 12] (r : b =[p] b₂) (r₂ : b₂ =[p₂] b₃) : b =[p ⬝ p₂] b₃ :=
  pathover.rec_on r₂ r

  definition inverseo [unfold 8] (r : b =[p] b₂) : b₂ =[p⁻¹] b :=
  pathover.rec_on r idpo

  definition apdo [unfold 6] (f : Πa, B a) (p : a = a₂) : f a =[p] f a₂ :=
  eq.rec_on p idpo

  definition oap [unfold 6] {C : A → Type} (f : Πa, B a → C a) (p : a = a₂) : f a =[p] f a₂ :=
  eq.rec_on p idpo

  definition concato_eq [unfold 10] (r : b =[p] b₂) (q : b₂ = b₂') : b =[p] b₂' :=
  eq.rec_on q r

  definition eq_concato [unfold 9] (q : b = b') (r : b' =[p] b₂) : b =[p] b₂ :=
  by induction q;exact r

  -- infix `⬝` := concato
  infix `⬝o`:75 := concato
  infix `⬝op`:75 := concato_eq
  infix `⬝po`:75 := eq_concato
  -- postfix `⁻¹` := inverseo
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

  definition cono.right_inv (r : b =[p] b₂) : r ⬝o r⁻¹ᵒ =[!con.right_inv] idpo :=
  pathover.rec_on r idpo

  definition cono.left_inv (r : b =[p] b₂) : r⁻¹ᵒ ⬝o r =[!con.left_inv] idpo :=
  pathover.rec_on r idpo

  definition eq_of_pathover {a' a₂' : A'} (q : a' =[p] a₂') : a' = a₂' :=
  by cases q;reflexivity

  definition pathover_of_eq {a' a₂' : A'} (q : a' = a₂') : a' =[p] a₂' :=
  by cases p;cases q;exact idpo

  definition pathover_constant [constructor] (p : a = a₂) (a' a₂' : A') : a' =[p] a₂' ≃ a' = a₂' :=
  begin
    fapply equiv.MK,
    { exact eq_of_pathover},
    { exact pathover_of_eq},
    { intro r, cases p, cases r, exact idp},
    { intro r, cases r, exact idp},
  end

  definition eq_of_pathover_idp [unfold 6] {b' : B a} (q : b =[idpath a] b') : b = b' :=
  tr_eq_of_pathover q

  --should B be explicit in the next two definitions?
  definition pathover_idp_of_eq [unfold 6] {b' : B a} (q : b = b') : b =[idpath a] b' :=
  eq.rec_on q idpo

  definition pathover_idp [constructor] (b : B a) (b' : B a) : b =[idpath a] b' ≃ b = b' :=
  equiv.MK eq_of_pathover_idp
           (pathover_idp_of_eq)
           (to_right_inv !pathover_equiv_tr_eq)
           (to_left_inv !pathover_equiv_tr_eq)


  -- definition pathover_idp (b : B a) (b' : B a) : b =[idpath a] b' ≃ b = b' :=
  -- pathover_equiv_tr_eq idp b b'

  -- definition eq_of_pathover_idp [reducible] {b' : B a} (q : b =[idpath a] b') : b = b' :=
  -- to_fun !pathover_idp q

  -- definition pathover_idp_of_eq [reducible] {b' : B a} (q : b = b') : b =[idpath a] b' :=
  -- to_inv !pathover_idp q

  definition idp_rec_on [recursor] {P : Π⦃b₂ : B a⦄, b =[idpath a] b₂ → Type}
    {b₂ : B a} (r : b =[idpath a] b₂) (H : P idpo) : P r :=
  have H2 : P (pathover_idp_of_eq (eq_of_pathover_idp r)), from
    eq.rec_on (eq_of_pathover_idp r) H,
  proof left_inv !pathover_idp r ▸ H2 qed

  definition rec_on_right [recursor] {P : Π⦃b₂ : B a₂⦄, b =[p] b₂ → Type}
    {b₂ : B a₂} (r : b =[p] b₂) (H : P !pathover_tr) : P r :=
  by cases r; exact H

  definition rec_on_left [recursor] {P : Π⦃b : B a⦄, b =[p] b₂ → Type}
    {b : B a} (r : b =[p] b₂) (H : P !tr_pathover) : P r :=
  by cases r; exact H

  --pathover with fibration B' ∘ f
  definition pathover_ap [unfold 10] (B' : A' → Type) (f : A → A') {p : a = a₂}
    {b : B' (f a)} {b₂ : B' (f a₂)} (q : b =[p] b₂) : b =[ap f p] b₂ :=
  by cases q; exact idpo

  definition pathover_of_pathover_ap (B' : A' → Type) (f : A → A') {p : a = a₂}
    {b : B' (f a)} {b₂ : B' (f a₂)} (q : b =[ap f p] b₂) : b =[p] b₂ :=
  by cases p; apply (idp_rec_on q); apply idpo

  definition pathover_compose (B' : A' → Type) (f : A → A') (p : a = a₂)
    (b : B' (f a)) (b₂ : B' (f a₂)) : b =[p] b₂ ≃ b =[ap f p] b₂ :=
  begin
    fapply equiv.MK,
    { apply pathover_ap},
    { apply pathover_of_pathover_ap},
    { intro q, cases p, esimp, apply (idp_rec_on q), apply idp},
    { intro q, cases q, exact idp},
  end

  definition apdo_con (f : Πa, B a) (p : a = a₂) (q : a₂ = a₃)
    : apdo f (p ⬝ q) = apdo f p ⬝o apdo f q :=
  by cases p; cases q; exact idp

  definition apdo_inv (f : Πa, B a) (p : a = a₂) : apdo f p⁻¹ = (apdo f p)⁻¹ᵒ :=
  by cases p; exact idp

  definition apdo_eq_pathover_of_eq_ap (f : A → A') (p : a = a₂) :
    apdo f p = pathover_of_eq (ap f p) :=
  eq.rec_on p idp

  definition pathover_of_pathover_tr (q : b =[p ⬝ p₂] p₂ ▸ b₂) : b =[p] b₂ :=
  by cases p₂;exact q

  definition pathover_tr_of_pathover {p : a = a₃} (q : b =[p ⬝ p₂⁻¹] b₂) : b =[p] p₂ ▸ b₂ :=
  by cases p₂;exact q

  definition pathover_tr_of_eq (q : b = b') : b =[p] p ▸ b' :=
  by cases q;apply pathover_tr

  definition tr_pathover_of_eq (q : b₂ = b₂') : p⁻¹ ▸ b₂ =[p] b₂' :=
  by cases q;apply tr_pathover

  definition apo011 (f : Πa, B a → A') (Ha : a = a₂) (Hb : b =[Ha] b₂)
      : f a b = f a₂ b₂ :=
  by cases Hb; exact idp

  definition apo0111 (f : Πa b, C a b → A') (Ha : a = a₂) (Hb : b =[Ha] b₂)
    (Hc : c =[apo011 C Ha Hb] c₂) : f a b c = f a₂ b₂ c₂ :=
  by cases Hb; apply (idp_rec_on Hc); apply idp

  definition apo11 {f : Πb, C a b} {g : Πb₂, C a₂ b₂} (r : f =[p] g)
    {b : B a} {b₂ : B a₂} (q : b =[p] b₂) : f b =[apo011 C p q] g b₂ :=
  by cases r; apply (idp_rec_on q); exact idpo

  definition apo10 {f : Πb, C a b} {g : Πb₂, C a₂ b₂} (r : f =[p] g)
    {b : B a} : f b =[apo011 C p !pathover_tr] g (p ▸ b) :=
  by cases r; exact idpo

  definition cono.right_inv_eq (q : b = b')
    : concato_eq (pathover_idp_of_eq q) q⁻¹ = (idpo : b =[refl a] b) :=
  by induction q;constructor

  definition cono.right_inv_eq' (q : b = b')
    : eq_concato q (pathover_idp_of_eq q⁻¹) = (idpo : b =[refl a] b) :=
  by induction q;constructor

  definition cono.left_inv_eq (q : b = b')
    : concato_eq (pathover_idp_of_eq q⁻¹) q = (idpo : b' =[refl a] b') :=
  by induction q;constructor

  definition cono.left_inv_eq' (q : b = b')
    : eq_concato q⁻¹ (pathover_idp_of_eq q) = (idpo : b' =[refl a] b') :=
  by induction q;constructor

  definition change_path (q : p = p') (r : b =[p] b₂) : b =[p'] b₂ :=
  by induction q;exact r

end eq
