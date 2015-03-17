/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: algebra.precategory.basic
Authors: Floris van Doorn
-/

open eq is_trunc

namespace category

  structure precategory [class] (ob : Type) : Type :=
    (hom : ob → ob → Type)
    (homH : Π(a b : ob), is_hset (hom a b))
    (comp : Π⦃a b c : ob⦄, hom b c → hom a b → hom a c)
    (ID : Π (a : ob), hom a a)
    (assoc : Π ⦃a b c d : ob⦄ (h : hom c d) (g : hom b c) (f : hom a b),
       comp h (comp g f) = comp (comp h g) f)
    (id_left : Π ⦃a b : ob⦄ (f : hom a b), comp !ID f = f)
    (id_right : Π ⦃a b : ob⦄ (f : hom a b), comp f !ID = f)

  attribute precategory [multiple-instances]
  attribute precategory.homH [instance]

  infixr `∘` := precategory.comp
  -- input ⟶ using \--> (this is a different arrow than \-> (→))
  infixl [parsing-only] `⟶`:25 := precategory.hom
  namespace hom
    infixl `⟶`:25 := precategory.hom -- if you open this namespace, hom a b is printed as a ⟶ b
  end hom

  abbreviation hom      := @precategory.hom
  abbreviation homH     := @precategory.homH
  abbreviation comp     := @precategory.comp
  abbreviation ID       := @precategory.ID
  abbreviation assoc    := @precategory.assoc
  abbreviation id_left  := @precategory.id_left
  abbreviation id_right := @precategory.id_right

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

    definition is_hprop_eq_hom [instance] : is_hprop (f = f') :=
    !is_trunc_eq

  end basic_lemmas
  context squares
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
  Precategory.mk a (precategory.mk b c d e f g h)

  abbreviation carrier := @Precategory.carrier

  attribute Precategory.carrier [coercion]
  attribute Precategory.struct [instance] [priority 10000] [coercion]
  -- definition precategory.carrier [coercion] [reducible] := Precategory.carrier
  -- definition precategory.struct [instance] [coercion] [reducible] := Precategory.struct
  notation g `∘⁅` C `⁆` f := @comp (Precategory.carrier C) (Precategory.struct C) _ _ _ g f
  -- TODO: make this left associative
  -- TODO: change this notation?

  definition Precategory.eta (C : Precategory) : Precategory.mk C C = C :=
  Precategory.rec (λob c, idp) C

end category
