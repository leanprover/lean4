/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn
-/

import hit.circle types.eq2 algebra.e_closure

open quotient eq circle sum sigma equiv function relation

namespace simple_two_quotient

  section
  parameters {A : Type}
             (R : A → A → Type)
  local abbreviation T := e_closure R -- the (type-valued) equivalence closure of R
  parameter  (Q : Π⦃a⦄, T a a → Type)
  variables ⦃a a' : A⦄ {s : R a a'} {r : T a a}


  local abbreviation B := A ⊎ Σ(a : A) (r : T a a), Q r

  inductive pre_simple_two_quotient_rel : B → B → Type :=
  | pre_Rmk {} : Π⦃a a'⦄ (r : R a a'), pre_simple_two_quotient_rel (inl a) (inl a')
  --BUG: if {} not provided, the alias for pre_Rmk is wrong

  definition pre_simple_two_quotient := quotient pre_simple_two_quotient_rel

  open pre_simple_two_quotient_rel
  local abbreviation C := quotient pre_simple_two_quotient_rel
  protected definition j [constructor] (a : A) : C := class_of pre_simple_two_quotient_rel (inl a)
  protected definition pre_aux [constructor] (q : Q r) : C :=
  class_of pre_simple_two_quotient_rel (inr ⟨a, r, q⟩)
  protected definition e (s : R a a') : j a = j a' := eq_of_rel _ (pre_Rmk s)
  protected definition et (t : T a a') : j a = j a' := e_closure.elim e t
  protected definition f [unfold-c 7] (q : Q r) : S¹ → C :=
  circle.elim (j a) (et r)

  protected definition pre_rec [unfold-c 8] {P : C → Type}
    (Pj : Πa, P (j a)) (Pa : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), P (pre_aux q))
    (Pe : Π⦃a a' : A⦄ (s : R a a'), Pj a =[e s] Pj a') (x : C) : P x :=
  begin
    induction x with p,
    { induction p,
      { apply Pj},
      { induction a with a1 a2, induction a2, apply Pa}},
    { induction H, esimp, apply Pe},
  end

  protected definition pre_elim [unfold-c 8] {P : Type} (Pj : A → P)
    (Pa : Π⦃a : A⦄ ⦃r : T a a⦄, Q r → P) (Pe : Π⦃a a' : A⦄ (s : R a a'), Pj a = Pj a') (x : C)
    : P :=
  pre_rec Pj Pa (λa a' s, pathover_of_eq (Pe s)) x

  protected theorem rec_e {P : C → Type}
    (Pj : Πa, P (j a)) (Pa : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), P (pre_aux q))
    (Pe : Π⦃a a' : A⦄ (s : R a a'), Pj a =[e s] Pj a') ⦃a a' : A⦄ (s : R a a')
    : apdo (pre_rec Pj Pa Pe) (e s) = Pe s :=
  !rec_eq_of_rel

  protected theorem elim_e {P : Type} (Pj : A → P) (Pa : Π⦃a : A⦄ ⦃r : T a a⦄, Q r → P)
    (Pe : Π⦃a a' : A⦄ (s : R a a'), Pj a = Pj a') ⦃a a' : A⦄ (s : R a a')
    : ap (pre_elim Pj Pa Pe) (e s) = Pe s :=
  begin
    apply eq_of_fn_eq_fn_inv !(pathover_constant (e s)),
    rewrite [▸*,-apdo_eq_pathover_of_eq_ap,↑pre_elim,rec_e],
  end

  protected definition elim_et {P : Type} (Pj : A → P) (Pa : Π⦃a : A⦄ ⦃r : T a a⦄, Q r → P)
    (Pe : Π⦃a a' : A⦄ (s : R a a'), Pj a = Pj a') ⦃a a' : A⦄ (t : T a a')
    : ap (pre_elim Pj Pa Pe) (et t) = e_closure.elim Pe t :=
  ap_e_closure_elim_h e (elim_e Pj Pa Pe) t

  inductive simple_two_quotient_rel : C → C → Type :=
  | Rmk {} : Π{a : A} {r : T a a} (q : Q r) (x : circle), simple_two_quotient_rel (f q x) (pre_aux q)

  open simple_two_quotient_rel
  definition simple_two_quotient := quotient simple_two_quotient_rel
  local abbreviation D := simple_two_quotient
  local abbreviation i := class_of simple_two_quotient_rel
  definition incl0 (a : A) : D := i (j a)
  protected definition aux (q : Q r) : D := i (pre_aux q)
  definition incl1 (s : R a a') : incl0 a = incl0 a' := ap i (e s)
  definition inclt (t : T a a') : incl0 a = incl0 a' := e_closure.elim incl1 t
  -- "wrong" version inclt, which is ap i (p ⬝ q) instead of ap i p ⬝ ap i q
  -- it is used in the proof, because inclt is easier to work with
  protected definition incltw (t : T a a') : incl0 a = incl0 a' := ap i (et t)

  protected definition inclt_eq_incltw (t : T a a') : inclt t = incltw t :=
  (ap_e_closure_elim i e t)⁻¹

  definition incl2' (q : Q r) (x : S¹) : i (f q x) = aux q :=
  eq_of_rel simple_two_quotient_rel (Rmk q x)

  protected definition incl2w (q : Q r) : incltw r = idp :=
  (ap02 i (elim_loop (j a) (et r))⁻¹) ⬝
  (ap_compose i (f q) loop)⁻¹ ⬝
  ap_weakly_constant (incl2' q) loop ⬝
  !con.right_inv

  definition incl2 (q : Q r) : inclt r = idp :=
  inclt_eq_incltw r ⬝ incl2w q

  local attribute simple_two_quotient f i incl0 aux incl1 incl2' inclt [reducible]
  local attribute i aux incl0 [constructor]
  protected definition elim {P : Type} (P0 : A → P)
    (P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a')
    (P2 : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), e_closure.elim P1 r = idp)
    (x : D) : P :=
  begin
    induction x,
    { refine (pre_elim _ _ _ a),
      { exact P0},
      { intro a r q, exact P0 a},
      { exact P1}},
    { exact abstract begin induction H, induction x,
      { exact idpath (P0 a)},
      { unfold f, apply pathover_eq, apply hdeg_square,
        exact abstract ap_compose (pre_elim P0 _ P1) (f q) loop ⬝
              ap _ !elim_loop ⬝
              !elim_et ⬝
              P2 q ⬝
              !ap_constant⁻¹ end
} end end},
  end
  local attribute elim [unfold-c 8]

  protected definition elim_on {P : Type} (x : D) (P0 : A → P)
    (P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a')
    (P2 : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), e_closure.elim P1 r = idp)
     : P :=
  elim P0 P1 P2 x

  definition elim_incl1 {P : Type} {P0 : A → P}
    {P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a'}
    (P2 : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), e_closure.elim P1 r = idp)
    ⦃a a' : A⦄ (s : R a a') : ap (elim P0 P1 P2) (incl1 s) = P1 s :=
  (ap_compose (elim P0 P1 P2) i (e s))⁻¹ ⬝ !elim_e

  definition elim_inclt {P : Type} {P0 : A → P}
    {P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a'}
    (P2 : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), e_closure.elim P1 r = idp)
    ⦃a a' : A⦄ (t : T a a') : ap (elim P0 P1 P2) (inclt t) = e_closure.elim P1 t :=
  ap_e_closure_elim_h incl1 (elim_incl1 P2) t

  protected definition elim_incltw {P : Type} {P0 : A → P}
    {P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a'}
    (P2 : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), e_closure.elim P1 r = idp)
    ⦃a a' : A⦄ (t : T a a') : ap (elim P0 P1 P2) (incltw t) = e_closure.elim P1 t :=
  (ap_compose (elim P0 P1 P2) i (et t))⁻¹ ⬝ !elim_et

  protected theorem elim_inclt_eq_elim_incltw {P : Type} {P0 : A → P}
    {P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a'}
    (P2 : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), e_closure.elim P1 r = idp)
    ⦃a a' : A⦄ (t : T a a')
    : elim_inclt P2 t = ap (ap (elim P0 P1 P2)) (inclt_eq_incltw t) ⬝ elim_incltw P2 t :=
  begin
    unfold [elim_inclt,elim_incltw,inclt_eq_incltw,et],
    refine !ap_e_closure_elim_h_eq ⬝ _,
    rewrite [ap_inv,-con.assoc],
    xrewrite [eq_of_square (ap_ap_e_closure_elim i (elim P0 P1 P2) e t)⁻¹ʰ],
    rewrite [↓incl1,con.assoc], apply whisker_left,
    rewrite [↑[elim_et,elim_incl1],+ap_e_closure_elim_h_eq,con_inv,↑[i,function.compose]],
    rewrite [-con.assoc (_ ⬝ _),con.assoc _⁻¹,con.left_inv,▸*,-ap_inv,-ap_con],
    apply ap (ap _),
    krewrite [-eq_of_homotopy3_inv,-eq_of_homotopy3_con]
  end

  definition elim_incl2'_incl0 {P : Type} {P0 : A → P}
    {P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a'}
    (P2 : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), e_closure.elim P1 r = idp)
    ⦃a : A⦄ ⦃r : T a a⦄ (q : Q r) : ap (elim P0 P1 P2) (incl2' q base) = idpath (P0 a) :=
  !elim_eq_of_rel

  -- set_option pp.implicit true
  protected theorem elim_incl2w {P : Type} (P0 : A → P)
    (P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a')
    (P2 : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), e_closure.elim P1 r = idp)
    ⦃a : A⦄ ⦃r : T a a⦄ (q : Q r)
    : square (ap02 (elim P0 P1 P2) (incl2w q)) (P2 q) (elim_incltw P2 r) idp :=
  begin
    esimp [incl2w,ap02],
    rewrite [+ap_con (ap _),▸*],
    xrewrite [-ap_compose (ap _) (ap i)],
    rewrite [+ap_inv],
    xrewrite [eq_top_of_square
               ((ap_compose_natural (elim P0 P1 P2) i (elim_loop (j a) (et r)))⁻¹ʰ⁻¹ᵛ ⬝h
               (ap_ap_compose (elim P0 P1 P2) i (f q) loop)⁻¹ʰ⁻¹ᵛ ⬝h
               ap_ap_weakly_constant (elim P0 P1 P2) (incl2' q) loop ⬝h
               ap_con_right_inv_sq (elim P0 P1 P2) (incl2' q base)),
               ↑[elim_incltw]],
    apply whisker_tl,
    rewrite [ap_weakly_constant_eq],
    xrewrite [naturality_apdo_eq (λx, !elim_eq_of_rel) loop],
    rewrite [↑elim_2,rec_loop,square_of_pathover_concato_eq,square_of_pathover_eq_concato,
            eq_of_square_vconcat_eq,eq_of_square_eq_vconcat],
    apply eq_vconcat,
    { apply ap (λx, _ ⬝ eq_con_inv_of_con_eq ((_ ⬝ x ⬝ _)⁻¹ ⬝ _) ⬝ _),
      transitivity _, apply ap eq_of_square,
        apply to_right_inv !pathover_eq_equiv_square (hdeg_square (elim_1 P A R Q P0 P1 a r q P2)),
      transitivity _, apply eq_of_square_hdeg_square,
      unfold elim_1, reflexivity},
    rewrite [+con_inv,whisker_left_inv,+inv_inv,-whisker_right_inv,
             con.assoc (whisker_left _ _),con.assoc _ (whisker_right _ _),▸*,
             whisker_right_con_whisker_left _ !ap_constant],
    xrewrite [-con.assoc _ _ (whisker_right _ _)],
    rewrite [con.assoc _ _ (whisker_left _ _),idp_con_whisker_left,▸*,
             con.assoc _ !ap_constant⁻¹,con.left_inv],
    xrewrite [eq_con_inv_of_con_eq_whisker_left,▸*],
    rewrite [+con.assoc _ _ !con.right_inv,
             right_inv_eq_idp (
               (λ(x : ap (elim P0 P1 P2) (incl2' q base) = idpath
               (elim P0 P1 P2 (class_of simple_two_quotient_rel (f q base)))), x)
                (elim_incl2'_incl0 P2 q)),
             ↑[whisker_left]],
    xrewrite [con2_con_con2],
    rewrite [idp_con,↑elim_incl2'_incl0,con.left_inv,whisker_right_inv,↑whisker_right],
    xrewrite [con.assoc _ _ (_ ◾ _)],
    rewrite [con.left_inv,▸*,-+con.assoc,con.assoc _⁻¹,↑[elim,function.compose],con.left_inv,
             ▸*,↑j,con.left_inv,idp_con],
    apply square_of_eq, reflexivity
  end

  theorem elim_incl2 {P : Type} (P0 : A → P)
    (P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a')
    (P2 : Π⦃a : A⦄ ⦃r : T a a⦄ (q : Q r), e_closure.elim P1 r = idp)
    ⦃a : A⦄ ⦃r : T a a⦄ (q : Q r)
    : square (ap02 (elim P0 P1 P2) (incl2 q)) (P2 q) (elim_inclt P2 r) idp :=
  begin
    rewrite [↑incl2,↑ap02,ap_con,elim_inclt_eq_elim_incltw],
    apply whisker_tl,
    apply elim_incl2w
  end

end
end simple_two_quotient

--attribute simple_two_quotient.j [constructor] --TODO
attribute /-simple_two_quotient.rec-/ simple_two_quotient.elim [unfold-c 8] [recursor 8]
--attribute simple_two_quotient.elim_type [unfold-c 9]
attribute /-simple_two_quotient.rec_on-/ simple_two_quotient.elim_on [unfold-c 5]
--attribute simple_two_quotient.elim_type_on [unfold-c 6]

namespace two_quotient
  open e_closure simple_two_quotient
  section
  parameters {A : Type}
             (R : A → A → Type)
  local abbreviation T := e_closure R -- the (type-valued) equivalence closure of R
  parameter  (Q : Π⦃a a'⦄, T a a' → T a a' → Type)
  variables ⦃a a' : A⦄ {s : R a a'} {t t' : T a a'}


  inductive two_quotient_Q : Π⦃a : A⦄, e_closure R a a → Type :=
  | Qmk : Π⦃a a' : A⦄ ⦃t t' : T a a'⦄, Q t t' → two_quotient_Q (t ⬝r t'⁻¹ʳ)
  open two_quotient_Q
  local abbreviation Q2 := two_quotient_Q

  definition two_quotient := simple_two_quotient R Q2
  definition incl0 (a : A) : two_quotient := incl0 _ _ a
  definition incl1 (s : R a a') : incl0 a = incl0 a' := incl1 _ _ s
  definition inclt (t : T a a') : incl0 a = incl0 a' := e_closure.elim incl1 t
  definition incl2 (q : Q t t') : inclt t = inclt t' :=
  eq_of_con_inv_eq_idp (incl2 _ _ (Qmk R q))

  protected definition elim {P : Type} (P0 : A → P)
    (P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a')
    (P2 : Π⦃a a' : A⦄ ⦃t t' : T a a'⦄ (q : Q t t'), e_closure.elim P1 t = e_closure.elim P1 t')
    (x : two_quotient) : P :=
  begin
    induction x,
    { exact P0 a},
    { exact P1 s},
    { exact abstract [unfold-c 10] begin induction q with a a' t t' q,
      rewrite [↑e_closure.elim,↓e_closure.elim P1 t,↓e_closure.elim P1 t'],
      apply con_inv_eq_idp, exact P2 q end end},
  end
  local attribute elim [unfold-c 8]

  protected definition elim_on {P : Type} (x : two_quotient) (P0 : A → P)
    (P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a')
    (P2 : Π⦃a a' : A⦄ ⦃t t' : T a a'⦄ (q : Q t t'), e_closure.elim P1 t = e_closure.elim P1 t')
     : P :=
  elim P0 P1 P2 x

  definition elim_incl1 {P : Type} {P0 : A → P}
    {P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a'}
    (P2 : Π⦃a a' : A⦄ ⦃t t' : T a a'⦄ (q : Q t t'), e_closure.elim P1 t = e_closure.elim P1 t')
    ⦃a a' : A⦄ (s : R a a') : ap (elim P0 P1 P2) (incl1 s) = P1 s :=
  !elim_incl1

  definition elim_inclt {P : Type} {P0 : A → P}
    {P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a'}
    (P2 : Π⦃a a' : A⦄ ⦃t t' : T a a'⦄ (q : Q t t'), e_closure.elim P1 t = e_closure.elim P1 t')
    ⦃a a' : A⦄ (t : T a a') : ap (elim P0 P1 P2) (inclt t) = e_closure.elim P1 t :=
  !elim_inclt --ap_e_closure_elim_h incl1 (elim_incl1 P2) t

  --print elim
  theorem elim_incl2 {P : Type} (P0 : A → P)
    (P1 : Π⦃a a' : A⦄ (s : R a a'), P0 a = P0 a')
    (P2 : Π⦃a a' : A⦄ ⦃t t' : T a a'⦄ (q : Q t t'), e_closure.elim P1 t = e_closure.elim P1 t')
    ⦃a a' : A⦄ ⦃t t' : T a a'⦄ (q : Q t t')
    : square (ap02 (elim P0 P1 P2) (incl2 q)) (P2 q) (elim_inclt P2 t) (elim_inclt P2 t') :=
  begin
    -- let H := elim_incl2 R Q2 P0 P1 (two_quotient_Q.rec (λ (a a' : A) (t t' : T a a') (q : Q t t'), con_inv_eq_idp (P2 q))) (Qmk R q),
    -- esimp at H,
    rewrite [↑[incl2,elim],ap_eq_of_con_inv_eq_idp],
    xrewrite [eq_top_of_square (elim_incl2 R Q2 P0 P1 (elim_1 A R Q P P0 P1 P2) (Qmk R q)),▸*],
    exact sorry
  end

end
end two_quotient

--attribute two_quotient.j [constructor] --TODO
attribute /-two_quotient.rec-/ two_quotient.elim [unfold-c 8] [recursor 8]
--attribute two_quotient.elim_type [unfold-c 9]
attribute /-two_quotient.rec_on-/ two_quotient.elim_on [unfold-c 5]
--attribute two_quotient.elim_type_on [unfold-c 6]
