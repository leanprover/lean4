/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Theorems about algebra specific to HoTT
-/

import .group arity types.pi prop_trunc types.unit .bundled

open equiv eq is_trunc unit

namespace algebra

  definition trivial_group [constructor] : group unit :=
  group.mk (λx y, star) _ (λx y z, idp) star (unit.rec idp) (unit.rec idp) (λx, star) (λx, idp)

  definition Trivial_group [constructor] : Group :=
  Group.mk _ trivial_group

  abbreviation G0 := Trivial_group

  open Group has_mul has_inv
  -- we prove under which conditions two groups are equal

  -- group and has_mul are classes. So, lean does not automatically generate
  -- coercions between them anymore.
  -- So, an application such as (@mul A G g h) in the following definition
  -- is type incorrect if the coercion is not added (explicitly or implicitly).
  definition group.to_has_mul {A : Type} (H : group A) : has_mul A := _
  local attribute group.to_has_mul group.to_has_inv [coercion]

  universe variable l
  variables {A B : Type.{l}}
  definition group_eq {G H : group A} (same_mul' : Π(g h : A), @mul A G g h = @mul A H g h)
    : G = H :=
  begin
    have foo : Π(g : A), @inv A G g = (@inv A G g * g) * @inv A H g,
      from λg, !mul_inv_cancel_right⁻¹,
    cases G with Gm Gs Gh1 G1 Gh2 Gh3 Gi Gh4,
    cases H with Hm Hs Hh1 H1 Hh2 Hh3 Hi Hh4,
    rewrite [↑[semigroup.to_has_mul,group.to_has_inv] at (same_mul',foo)],
    have same_mul : Gm = Hm, from eq_of_homotopy2 same_mul',
    cases same_mul,
    have same_one : G1 = H1, from calc
      G1 = Hm G1 H1 : Hh3
     ... = H1 : Gh2,
    have same_inv : Gi = Hi, from eq_of_homotopy (take g, calc
      Gi g = Hm (Hm (Gi g) g) (Hi g) : foo
       ... = Hm G1 (Hi g) : by rewrite Gh4
       ... = Hi g : Gh2),
    cases same_one, cases same_inv,
    have ps  : Gs  = Hs,  from !is_prop.elim,
    have ph1 : Gh1 = Hh1, from !is_prop.elim,
    have ph2 : Gh2 = Hh2, from !is_prop.elim,
    have ph3 : Gh3 = Hh3, from !is_prop.elim,
    have ph4 : Gh4 = Hh4, from !is_prop.elim,
    cases ps, cases ph1, cases ph2, cases ph3, cases ph4, reflexivity
  end

  definition group_pathover {G : group A} {H : group B} {p : A = B}
    (resp_mul : Π(g h : A), cast p (g * h) = cast p g * cast p h) : G =[p] H :=
  begin
    induction p,
    apply pathover_idp_of_eq, exact group_eq (resp_mul)
  end

  definition Group_eq_of_eq {G H : Group} (p : carrier G = carrier H)
    (resp_mul : Π(g h : G), cast p (g * h) = cast p g * cast p h) : G = H :=
  begin
    cases G with Gc G, cases H with Hc H,
    apply (apo011 mk p),
    exact group_pathover resp_mul
  end

  definition Group_eq {G H : Group} (f : carrier G ≃ carrier H)
    (resp_mul : Π(g h : G), f (g * h) = f g * f h) : G = H :=
  Group_eq_of_eq (ua f) (λg h, !cast_ua ⬝ resp_mul g h ⬝ ap011 mul !cast_ua⁻¹ !cast_ua⁻¹)

  definition trivial_group_of_is_contr (G : Group) [H : is_contr G] : G = G0 :=
  begin
    fapply Group_eq,
    { apply equiv_unit_of_is_contr},
    { intros, reflexivity}
  end

end algebra
