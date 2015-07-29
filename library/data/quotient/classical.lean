/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

A classical treatment of quotients, using Hilbert choice.
-/
import algebra.relation data.subtype logic.choice
import .basic

namespace quotient

open relation nonempty subtype

/- abstract quotient -/

noncomputable definition prelim_map {A : Type} (R : A → A → Prop) (a : A) :=
-- TODO: it is interesting how the elaborator fails here
-- epsilon (fun b, R a b)
@epsilon _ (nonempty.intro a) (fun b, R a b)

-- TODO: only needed R reflexive (or weaker: R a a)
theorem prelim_map_rel {A : Type} {R : A → A → Prop} (H : is_equivalence R) (a : A)
  : R a (prelim_map R a) :=
have reflR : reflexive R, from is_equivalence.refl R,
epsilon_spec (exists.intro a (reflR a))

-- TODO: only needed: R PER
theorem prelim_map_congr {A : Type} {R : A → A → Prop} (H1 : is_equivalence R) {a b : A}
  (H2 : R a b) : prelim_map R a = prelim_map R b :=
have symmR : relation.symmetric R, from is_equivalence.symm R,
have transR : relation.transitive R, from is_equivalence.trans R,
have H3 : ∀c, R a c ↔ R b c, from
  take c,
    iff.intro
      (assume H4 : R a c, transR (symmR H2) H4)
      (assume H4 : R b c, transR H2 H4),
have H4 : (fun c, R a c) = (fun c, R b c), from
  funext (take c, eq.of_iff (H3 c)),
assert H5 : nonempty A, from
  nonempty.intro a,
show epsilon (λc, R a c) = epsilon (λc, R b c), from
  congr_arg _ H4

noncomputable definition quotient {A : Type} (R : A → A → Prop) : Type := image (prelim_map R)

noncomputable definition quotient_abs {A : Type} (R : A → A → Prop) : A → quotient R :=
fun_image (prelim_map R)

noncomputable definition quotient_elt_of {A : Type} (R : A → A → Prop) : quotient R → A := elt_of

theorem quotient_is_quotient  {A : Type} (R : A → A → Prop) (H : is_equivalence R)
  : is_quotient R (quotient_abs R) (quotient_elt_of R) :=
representative_map_to_quotient_equiv
  H
  (prelim_map_rel H)
  (@prelim_map_congr _ _ H)

end quotient
