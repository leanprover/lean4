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

/-
  We take two higher inductive types (hits) as primitive notions in Lean. We define all other hits
  in terms of these two hits. The hits which are primitive are
    - n-truncation
    - general colimits
  For each of the hits we add the following constants:
    - the type formation
    - the term and path constructors
    - the dependent recursor
  We add the computation rule for point constructors judgmentally to the kernel of Lean, and for the
  path constructors (undecided).

  In this file we only define the dependent recursor. For the nondependent recursor and all other
  uses of these hits, see the folder /hott/hit/
-/

constant trunc.{u} (n : trunc_index) (A : Type.{u}) : Type.{u}

namespace trunc

  constant tr {n : trunc_index} {A : Type} (a : A) : trunc n A
  constant is_trunc_trunc (n : trunc_index) (A : Type) : is_trunc n (trunc n A)

  attribute is_trunc_trunc [instance]

  /-protected-/ constant rec {n : trunc_index} {A : Type} {P : trunc n A → Type}
    [Pt : Πaa, is_trunc n (P aa)] (H : Πa, P (tr a)) : Πaa, P aa

  protected definition rec_on [reducible] {n : trunc_index} {A : Type} {P : trunc n A → Type}
    (aa : trunc n A) [Pt : Πaa, is_trunc n (P aa)] (H : Πa, P (tr a)) : P aa :=
  trunc.rec H aa

  definition rec_tr [reducible] {n : trunc_index} {A : Type} {P : trunc n A → Type}
    [Pt : Πaa, is_trunc n (P aa)] (H : Πa, P (tr a)) (a : A) : trunc.rec H (tr a) = H a :=
  sorry --idp

end trunc

namespace colimit
structure diagram [class] :=
  (Iob : Type)
  (Ihom : Type)
  (ob : Iob → Type)
  (dom cod : Ihom → Iob)
  (hom : Π(j : Ihom), ob (dom j) → ob (cod j))
end colimit
open colimit colimit.diagram

constant colimit.{u v w} : diagram.{u v w} → Type.{max u v w}

namespace colimit

  constant inclusion : Π [D : diagram] {i : Iob}, ob i → colimit D
  abbreviation ι := @inclusion

  constant cglue : Π [D : diagram] (j : Ihom) (x : ob (dom j)), ι (hom j x) = ι x

  /-protected-/ constant rec : Π [D : diagram] {P : colimit D → Type}
    (Pincl : Π⦃i : Iob⦄ (x : ob i), P (ι x))
    (Pglue : Π(j : Ihom) (x : ob (dom j)), cglue j x ▹ Pincl (hom j x) = Pincl x)
      (y : colimit D), P y

  definition rec_incl [reducible] [D : diagram] {P : colimit D → Type}
    (Pincl : Π⦃i : Iob⦄ (x : ob i), P (ι x))
    (Pglue : Π(j : Ihom) (x : ob (dom j)), cglue j x ▹ Pincl (hom j x) = Pincl x)
      {i : Iob} (x : ob i) : rec Pincl Pglue (ι x) = Pincl x :=
  sorry --idp

  definition rec_cglue [reducible] [D : diagram] {P : colimit D → Type}
    (Pincl : Π⦃i : Iob⦄ (x : ob i), P (ι x))
    (Pglue : Π(j : Ihom) (x : ob (dom j)), cglue j x ▹ Pincl (hom j x) = Pincl x)
      {j : Ihom} (x : ob (dom j)) : apD (rec Pincl Pglue) (cglue j x) = sorry ⬝ Pglue j x ⬝ sorry :=
  --the sorry's in the statement can be removed when rec_incl is definitional
  sorry

  protected definition rec_on [reducible] [D : diagram] {P : colimit D → Type} (y : colimit D)
    (Pincl : Π⦃i : Iob⦄ (x : ob i), P (ι x))
    (Pglue : Π(j : Ihom) (x : ob (dom j)), cglue j x ▹ Pincl (hom j x) = Pincl x) : P y :=
  colimit.rec Pincl Pglue y

end colimit
