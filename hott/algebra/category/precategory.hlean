/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: algebra.category.precategory
Authors: Floris van Doorn
-/
import types.trunc types.pi arity

open eq is_trunc pi

namespace category

/-
  Just as in Coq-HoTT we add two redundant fields to precategories: assoc' and id_id.
  The first is to make (Cᵒᵖ)ᵒᵖ = C definitionally when C is a constructor.
  The second is to ensure that the functor from the terminal category 1 ⇒ Cᵒᵖ is
    opposite to the functor 1 ⇒ C.
-/

  structure precategory [class] (ob : Type) : Type :=
  mk' ::
    (hom : ob → ob → Type)
    (comp : Π⦃a b c : ob⦄, hom b c → hom a b → hom a c)
    (ID : Π (a : ob), hom a a)
    (assoc  : Π ⦃a b c d : ob⦄ (h : hom c d) (g : hom b c) (f : hom a b),
       comp h (comp g f) = comp (comp h g) f)
    (assoc' : Π ⦃a b c d : ob⦄ (h : hom c d) (g : hom b c) (f : hom a b),
       comp (comp h g) f = comp h (comp g f))
    (id_left : Π ⦃a b : ob⦄ (f : hom a b), comp !ID f = f)
    (id_right : Π ⦃a b : ob⦄ (f : hom a b), comp f !ID = f)
    (id_id : Π (a : ob), comp !ID !ID = ID a)
    (is_hset_hom : Π(a b : ob), is_hset (hom a b))

  attribute precategory [multiple-instances]
  attribute precategory.is_hset_hom [instance]

  infixr `∘` := precategory.comp
  -- input ⟶ using \--> (this is a different arrow than \-> (→))
  infixl [parsing-only] `⟶`:25 := precategory.hom
  namespace hom
    infixl `⟶`:25 := precategory.hom -- if you open this namespace, hom a b is printed as a ⟶ b
  end hom

  abbreviation hom         := @precategory.hom
  abbreviation comp        := @precategory.comp
  abbreviation ID          := @precategory.ID
  abbreviation assoc       := @precategory.assoc
  abbreviation assoc'      := @precategory.assoc'
  abbreviation id_left     := @precategory.id_left
  abbreviation id_right    := @precategory.id_right
  abbreviation id_id       := @precategory.id_id
  abbreviation is_hset_hom := @precategory.is_hset_hom

  -- the constructor you want to use in practice
  protected definition precategory.mk {ob : Type} (hom : ob → ob → Type)
    [hset : Π (a b : ob), is_hset (hom a b)]
    (comp : Π ⦃a b c : ob⦄, hom b c → hom a b → hom a c) (ID : Π (a : ob), hom a a)
    (ass : Π ⦃a b c d : ob⦄ (h : hom c d) (g : hom b c) (f : hom a b),
       comp h (comp g f) = comp (comp h g) f)
    (idl : Π ⦃a b : ob⦄ (f : hom a b), comp (ID b) f = f)
    (idr : Π ⦃a b : ob⦄ (f : hom a b), comp f (ID a) = f) : precategory ob :=
  precategory.mk' hom comp ID ass (λa b c d h g f, !ass⁻¹) idl idr (λa, !idl) hset

  section basic_lemmas
    variables {ob : Type} [C : precategory ob]
    variables {a b c d : ob} {h : c ⟶ d} {g : hom b c} {f f' : hom a b} {i : a ⟶ a}
    include C

    definition id [reducible] := ID a

    definition id_comp (a : ob) : ID a ∘ ID a = ID a := !id_left

    definition id_leftright       (f : hom a b) : id ∘ f ∘ id = f := !id_left ⬝ !id_right
    definition comp_id_eq_id_comp (f : hom a b) : f ∘ id = id ∘ f := !id_right ⬝ !id_left⁻¹

    definition left_id_unique (H : Π{b} {f : hom b a}, i ∘ f = f) : i = id :=
    calc i = i ∘ id : by rewrite id_right
       ... = id     : by rewrite H

    definition right_id_unique (H : Π{b} {f : hom a b}, f ∘ i = f) : i = id :=
    calc i = id ∘ i : by rewrite id_left
       ... = id     : by rewrite H

    definition homset [reducible] (x y : ob) : hset :=
    hset.mk (hom x y) _

  end basic_lemmas
  section squares
    parameters {ob : Type} [C : precategory ob]
    local infixl `⟶`:25 := @precategory.hom ob C
    local infixr `∘`    := @precategory.comp ob C _ _ _
    definition compose_squares {xa xb xc ya yb yc : ob}
      {xg : xb ⟶ xc} {xf : xa ⟶ xb} {yg : yb ⟶ yc} {yf : ya ⟶ yb}
      {wa : xa ⟶ ya} {wb : xb ⟶ yb} {wc : xc ⟶ yc}
      (xyab : wb ∘ xf = yf ∘ wa) (xybc : wc ∘ xg = yg ∘ wb)
        : wc ∘ (xg ∘ xf) = (yg ∘ yf) ∘ wa :=
    calc
      wc ∘ (xg ∘ xf) = (wc ∘ xg) ∘ xf : by rewrite assoc
        ... = (yg ∘ wb) ∘ xf : by rewrite xybc
        ... = yg ∘ (wb ∘ xf) : by rewrite assoc
        ... = yg ∘ (yf ∘ wa) : by rewrite xyab
        ... = (yg ∘ yf) ∘ wa : by rewrite assoc

    definition compose_squares_2x2 {xa xb xc ya yb yc za zb zc : ob}
      {xg : xb ⟶ xc} {xf : xa ⟶ xb} {yg : yb ⟶ yc} {yf : ya ⟶ yb} {zg : zb ⟶ zc} {zf : za ⟶ zb}
      {va : ya ⟶ za} {vb : yb ⟶ zb} {vc : yc ⟶ zc} {wa : xa ⟶ ya} {wb : xb ⟶ yb} {wc : xc ⟶ yc}
      (xyab : wb ∘ xf = yf ∘ wa) (xybc : wc ∘ xg = yg ∘ wb)
      (yzab : vb ∘ yf = zf ∘ va) (yzbc : vc ∘ yg = zg ∘ vb)
        : (vc ∘ wc) ∘ (xg ∘ xf) = (zg ∘ zf) ∘ (va ∘ wa) :=
    calc
      (vc ∘ wc) ∘ (xg ∘ xf) = vc ∘ (wc ∘ (xg ∘ xf)) : by rewrite (assoc vc wc _)
        ... = vc ∘ ((yg ∘ yf) ∘ wa) : by rewrite (compose_squares xyab xybc)
        ... = (vc ∘ (yg ∘ yf)) ∘ wa : by rewrite assoc
        ... = ((zg ∘ zf) ∘ va) ∘ wa : by rewrite (compose_squares yzab yzbc)
        ... = (zg ∘ zf) ∘ (va ∘ wa) : by rewrite assoc

    definition square_precompose {xa xb xc yb yc : ob}
      {xg : xb ⟶ xc} {yg : yb ⟶ yc} {wb : xb ⟶ yb} {wc : xc ⟶ yc}
      (H : wc ∘ xg = yg ∘ wb) (xf : xa ⟶ xb) : wc ∘ xg ∘ xf = yg ∘ wb ∘ xf :=
    calc
      wc ∘ xg ∘ xf = (wc ∘ xg) ∘ xf : by rewrite assoc
        ... = (yg ∘ wb) ∘ xf        : by rewrite H
        ... = yg ∘ wb ∘ xf          : by rewrite assoc

    definition square_postcompose {xb xc yb yc yd : ob}
      {xg : xb ⟶ xc} {yg : yb ⟶ yc} {wb : xb ⟶ yb} {wc : xc ⟶ yc}
      (H : wc ∘ xg = yg ∘ wb) (yh : yc ⟶ yd) : (yh ∘ wc) ∘ xg = (yh ∘ yg) ∘ wb :=
    calc
      (yh ∘ wc) ∘ xg = yh ∘ wc ∘ xg : by rewrite assoc
        ... = yh ∘ yg ∘ wb          : by rewrite H
        ... = (yh ∘ yg) ∘ wb        : by rewrite assoc

    definition square_prepostcompose {xa xb xc yb yc yd : ob}
      {xg : xb ⟶ xc} {yg : yb ⟶ yc} {wb : xb ⟶ yb} {wc : xc ⟶ yc}
      (H : wc ∘ xg = yg ∘ wb) (yh : yc ⟶ yd) (xf : xa ⟶ xb)
        : (yh ∘ wc) ∘ (xg ∘ xf) = (yh ∘ yg) ∘ (wb ∘ xf)  :=
    square_precompose (square_postcompose H yh) xf
  end squares

  structure Precategory : Type :=
    (carrier : Type)
    (struct : precategory carrier)

  definition precategory.Mk [reducible] {ob} (C) : Precategory := Precategory.mk ob C
  definition precategory.MK [reducible] (a b c d e f g h) : Precategory :=
  Precategory.mk a (@precategory.mk _ b c d e f g h)

  abbreviation carrier := @Precategory.carrier

  attribute Precategory.carrier [coercion]
  attribute Precategory.struct [instance] [priority 10000] [coercion]
  -- definition precategory.carrier [coercion] [reducible] := Precategory.carrier
  -- definition precategory.struct [instance] [coercion] [reducible] := Precategory.struct
  notation g `∘⁅`:60 C:0 `⁆`:0 f:60 :=
  @comp (Precategory.carrier C) (Precategory.struct C) _ _ _ g f
  -- TODO: make this left associative
  -- TODO: change this notation?

  definition Precategory.eta (C : Precategory) : Precategory.mk C C = C :=
  Precategory.rec (λob c, idp) C

  /-Characterization of paths between precategories-/

  definition precategory_mk'_eq (ob : Type)
    (hom1 : ob → ob → Type)
    (hom2 : ob → ob → Type)
    (homH1 : Π(a b : ob), is_hset (hom1 a b))
    (homH2 : Π(a b : ob), is_hset (hom2 a b))
    (comp1 : Π⦃a b c : ob⦄, hom1 b c → hom1 a b → hom1 a c)
    (comp2 : Π⦃a b c : ob⦄, hom2 b c → hom2 a b → hom2 a c)
    (ID1 : Π (a : ob), hom1 a a)
    (ID2 : Π (a : ob), hom2 a a)
    (assoc1 : Π ⦃a b c d : ob⦄ (h : hom1 c d) (g : hom1 b c) (f : hom1 a b),
       comp1 h (comp1 g f) = comp1 (comp1 h g) f)
    (assoc2 : Π ⦃a b c d : ob⦄ (h : hom2 c d) (g : hom2 b c) (f : hom2 a b),
       comp2 h (comp2 g f) = comp2 (comp2 h g) f)
    (assoc1' : Π ⦃a b c d : ob⦄ (h : hom1 c d) (g : hom1 b c) (f : hom1 a b),
       comp1 (comp1 h g) f = comp1 h (comp1 g f))
    (assoc2' : Π ⦃a b c d : ob⦄ (h : hom2 c d) (g : hom2 b c) (f : hom2 a b),
       comp2 (comp2 h g) f = comp2 h (comp2 g f))
    (id_left1 : Π ⦃a b : ob⦄ (f : hom1 a b), comp1 !ID1 f = f)
    (id_left2 : Π ⦃a b : ob⦄ (f : hom2 a b), comp2 !ID2 f = f)
    (id_right1 : Π ⦃a b : ob⦄ (f : hom1 a b), comp1 f !ID1 = f)
    (id_right2 : Π ⦃a b : ob⦄ (f : hom2 a b), comp2 f !ID2 = f)
    (id_id1 : Π (a : ob), comp1 !ID1 !ID1 = ID1 a)
    (id_id2 : Π (a : ob), comp2 !ID2 !ID2 = ID2 a)
    (p : hom1 = hom2)
    (q : p ▹ comp1 = comp2)
    (r : p ▹ ID1 = ID2) :
    precategory.mk' hom1 comp1 ID1 assoc1 assoc1' id_left1 id_right1 id_id1 homH1
    = precategory.mk' hom2 comp2 ID2 assoc2 assoc2' id_left2 id_right2 id_id2 homH2 :=
  begin
    cases p, cases q, cases r,
    apply (ap0111111 (precategory.mk' hom2 comp2 ID2)),
    repeat (apply is_hprop.elim),
  end

  definition precategory_eq (ob : Type)
    (C D : precategory ob)
    (p : @hom ob C = @hom ob D)
    (q : transport (λ x, Πa b c, x b c → x a b → x a c) p
           (@comp ob C) = @comp ob D)
    (r : transport (λ x, Πa, x a a) p (@ID ob C) = @ID ob D) : C = D :=
  begin
    cases C, cases D,
    apply precategory_mk'_eq, apply q, apply r,
  end

  definition precategory_mk_eq (ob : Type)
    (hom1 : ob → ob → Type)
    (hom2 : ob → ob → Type)
    (homH1 : Π(a b : ob), is_hset (hom1 a b))
    (homH2 : Π(a b : ob), is_hset (hom2 a b))
    (comp1 : Π⦃a b c : ob⦄, hom1 b c → hom1 a b → hom1 a c)
    (comp2 : Π⦃a b c : ob⦄, hom2 b c → hom2 a b → hom2 a c)
    (ID1 : Π (a : ob), hom1 a a)
    (ID2 : Π (a : ob), hom2 a a)
    (assoc1 : Π ⦃a b c d : ob⦄ (h : hom1 c d) (g : hom1 b c) (f : hom1 a b),
       comp1 h (comp1 g f) = comp1 (comp1 h g) f)
    (assoc2 : Π ⦃a b c d : ob⦄ (h : hom2 c d) (g : hom2 b c) (f : hom2 a b),
       comp2 h (comp2 g f) = comp2 (comp2 h g) f)
    (id_left1 : Π ⦃a b : ob⦄ (f : hom1 a b), comp1 !ID1 f = f)
    (id_left2 : Π ⦃a b : ob⦄ (f : hom2 a b), comp2 !ID2 f = f)
    (id_right1 : Π ⦃a b : ob⦄ (f : hom1 a b), comp1 f !ID1 = f)
    (id_right2 : Π ⦃a b : ob⦄ (f : hom2 a b), comp2 f !ID2 = f)
    (p : Π (a b : ob), hom1 a b = hom2 a b)
    (q : transport (λ x, Π a b c, x b c → x a b → x a c)
      (eq_of_homotopy (λ a, eq_of_homotopy (λ b, p a b))) @comp1 = @comp2)
    (r : transport (λ x, Π a, x a a)
      (eq_of_homotopy (λ (x : ob), eq_of_homotopy (λ (x_1 : ob), p x x_1)))
         ID1 = ID2) :
    precategory.mk hom1 comp1 ID1 assoc1 id_left1 id_right1
    = precategory.mk hom2 comp2 ID2 assoc2 id_left2 id_right2 :=
  begin
    fapply precategory_eq,
        apply eq_of_homotopy, intros,
        apply eq_of_homotopy, intros,
        exact (p _ _),
      exact q,
    exact r,
  end

  definition Precategory_eq (C D : Precategory)
    (p : carrier C = carrier D)
    (q : p ▹ (Precategory.struct C) = Precategory.struct D) : C = D :=
  begin
    cases C, cases D,
    cases p, cases q,
    apply idp,
  end

end category
