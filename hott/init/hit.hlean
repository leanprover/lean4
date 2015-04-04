/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: init.hit
Authors: Floris van Doorn

Declaration of the primitive hits in Lean
-/

prelude

import .trunc

open is_trunc eq

constant trunc.{u} (n : trunc_index) (A : Type.{u}) : Type.{u}

namespace trunc

  constant tr {n : trunc_index} {A : Type} (a : A) : trunc n A
  constant is_trunc_trunc (n : trunc_index) (A : Type) : is_trunc n (trunc n A)

  attribute is_trunc_trunc [instance]

  /-protected-/ constant rec {n : trunc_index} {A : Type} {P : trunc n A → Type}
    [Pt : Πaa, is_trunc n (P aa)] (H : Πa, P (tr a)) : Πaa, P aa

  protected definition rec_on {n : trunc_index} {A : Type} {P : trunc n A → Type} (aa : trunc n A)
    [Pt : Πaa, is_trunc n (P aa)] (H : Πa, P (tr a)) : P aa :=
  trunc.rec H aa

  definition comp_tr {n : trunc_index} {A : Type} {P : trunc n A → Type}
    [Pt : Πaa, is_trunc n (P aa)] (H : Πa, P (tr a)) (a : A) : trunc.rec H (tr a) = H a :=
  sorry --idp

end trunc

constant cylinder.{u v} {A : Type.{u}} {B : Type.{v}} (f : A → B) : B → Type.{max u v}

namespace cylinder

  constant base {A B : Type} (f : A → B) (b : B) : cylinder f b
  constant top  {A B : Type} (f : A → B) (a : A) : cylinder f (f a)
  constant seg  {A B : Type} (f : A → B) (a : A) : top f a = base f (f a)

  axiom is_trunc_trunc (n : trunc_index) (A : Type) : is_trunc n (trunc n A)

  attribute is_trunc_trunc [instance]

  /-protected-/ constant rec {A B : Type} {f : A → B} {P : Π{b : B}, cylinder f b → Type}
    (Pbase : Π(b : B), P (base f b)) (Ptop  : Π(a : A), P (top f a))
    (Pseg  : Π(a : A), seg f a ▹ Ptop a = Pbase (f a))
      : Π{b : B} (x : cylinder f b), P x

  protected definition rec_on {A B : Type} {f : A → B} {P : Π{b : B}, cylinder f b → Type}
    {b : B} (x : cylinder f b) (Pbase : Π(b : B), P (base f b)) (Ptop  : Π(a : A), P (top f a))
    (Pseg  : Π(a : A), seg f a ▹ Ptop a = Pbase (f a)) : P x :=
  cylinder.rec Pbase Ptop Pseg x

  definition comp_base {A B : Type} {f : A → B} {P : Π{b : B}, cylinder f b → Type}
    (Pbase : Π(b : B), P (base f b)) (Ptop  : Π(a : A), P (top f a))
    (Pseg  : Π(a : A), seg f a ▹ Ptop a = Pbase (f a)) (b : B) :
      cylinder.rec Pbase Ptop Pseg (base f b) = Pbase b :=
  sorry --idp

  definition comp_top {A B : Type} {f : A → B} {P : Π{b : B}, cylinder f b → Type}
    (Pbase : Π(b : B), P (base f b)) (Ptop  : Π(a : A), P (top f a))
    (Pseg  : Π(a : A), seg f a ▹ Ptop a = Pbase (f a)) (a : A) :
      cylinder.rec Pbase Ptop Pseg (top f a) = Ptop a :=
  sorry --idp

  definition comp_seg {A B : Type} {f : A → B} {P : Π{b : B}, cylinder f b → Type}
    (Pbase : Π(b : B), P (base f b)) (Ptop  : Π(a : A), P (top f a))
    (Pseg  : Π(a : A), seg f a ▹ Ptop a = Pbase (f a)) (a : A) :
      apD (cylinder.rec Pbase Ptop Pseg) (seg f a) = sorry ⬝ Pseg a ⬝ sorry :=
  --the sorry's in the statement can be removed when comp_base/comp_top are definitional
  sorry

end cylinder


namespace colimit
structure diagram [class] :=
  (Iob : Type)
  (Ihom : Type)
  (ob : Iob → Type)
  (dom cod : Ihom → Iob)
  (hom : Π(j : Ihom), ob (dom j) → ob (cod j))
end colimit
open eq colimit colimit.diagram

constant colimit.{u v w} : diagram.{u v w} → Type.{max u v w}

namespace colimit

  constant inclusion : Π [D : diagram] {i : Iob}, ob i → colimit D
  abbreviation ι := @inclusion

  constant cglue : Π [D : diagram] (j : Ihom) (x : ob (dom j)), ι (hom j x) = ι x

  /-protected-/ constant rec : Π [D : diagram] {P : colimit D → Type}
    (Pincl : Π⦃i : Iob⦄ (x : ob i), P (ι x))
    (Pglue : Π(j : Ihom) (x : ob (dom j)), cglue j x ▹ Pincl (hom j x) = Pincl x)
      (y : colimit D), P y

  definition comp_incl [D : diagram] {P : colimit D → Type}
    (Pincl : Π⦃i : Iob⦄ (x : ob i), P (ι x))
    (Pglue : Π(j : Ihom) (x : ob (dom j)), cglue j x ▹ Pincl (hom j x) = Pincl x)
      {i : Iob} (x : ob i) : rec Pincl Pglue (ι x) = Pincl x :=
  sorry --idp

  definition comp_cglue [D : diagram] {P : colimit D → Type}
    (Pincl : Π⦃i : Iob⦄ (x : ob i), P (ι x))
    (Pglue : Π(j : Ihom) (x : ob (dom j)), cglue j x ▹ Pincl (hom j x) = Pincl x)
      {j : Ihom} (x : ob (dom j)) : apD (rec Pincl Pglue) (cglue j x) = sorry ⬝ Pglue j x ⬝ sorry :=
  --the sorry's in the statement can be removed when comp_incl is definitional
  sorry

  protected definition rec_on [D : diagram] {P : colimit D → Type} (y : colimit D)
    (Pincl : Π⦃i : Iob⦄ (x : ob i), P (ι x))
    (Pglue : Π(j : Ihom) (x : ob (dom j)), cglue j x ▹ Pincl (hom j x) = Pincl x) : P y :=
  colimit.rec Pincl Pglue y

end colimit

exit
--ALTERNATIVE: COLIMIT without definition "diagram"
constant colimit.{u v w} : Π {I : Type.{u}} {J : Type.{v}} (ob : I → Type.{w}) {dom : J → I}
  {cod : J → I} (hom : Π⦃j : J⦄, ob (dom j) → ob (cod j)), Type.{max u v w}

namespace colimit

  constant inclusion : Π {I J : Type} {ob : I → Type} {dom : J → I} {cod : J → I}
    (hom : Π⦃j : J⦄, ob (dom j) → ob (cod j)) {i : I}, ob i → colimit ob hom
  abbreviation ι := @inclusion

  constant glue : Π {I J : Type} {ob : I → Type} {dom : J → I} {cod : J → I}
    (hom : Π⦃j : J⦄, ob (dom j) → ob (cod j)) (j : J) (a : ob (dom j)), ι hom (hom a) = ι hom a

  /-protected-/ constant rec : Π {I J : Type} {ob : I → Type} {dom : J → I} {cod : J → I}
    (hom : Π⦃j : J⦄, ob (dom j) → ob (cod j)) {P : colimit ob hom → Type}
 -- ...
end colimit
