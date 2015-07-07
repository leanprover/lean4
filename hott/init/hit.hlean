/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Declaration of the primitive hits in Lean
-/

prelude

import .trunc .pathover

open is_trunc eq

/-
  We take two higher inductive types (hits) as primitive notions in Lean. We define all other hits
  in terms of these two hits. The hits which are primitive are
    - n-truncation
    - quotients (not truncated)
  For each of the hits we add the following constants:
    - the type formation
    - the term and path constructors
    - the dependent recursor
  We add the computation rule for point constructors judgmentally to the kernel of Lean.
  The computation rules for the path constructors are added (propositionally) as axioms

  In this file we only define the dependent recursor. For the nondependent recursor and all other
  uses of these hits, see the folder ../hit/
-/

constant trunc.{u} (n : trunc_index) (A : Type.{u}) : Type.{u}

namespace trunc
  constant tr {n : trunc_index} {A : Type} (a : A) : trunc n A
  constant is_trunc_trunc (n : trunc_index) (A : Type) : is_trunc n (trunc n A)

  attribute is_trunc_trunc [instance]

  protected constant rec {n : trunc_index} {A : Type} {P : trunc n A → Type}
    [Pt : Πaa, is_trunc n (P aa)] (H : Πa, P (tr a)) : Πaa, P aa

  protected definition rec_on [reducible] {n : trunc_index} {A : Type}
    {P : trunc n A → Type} (aa : trunc n A) [Pt : Πaa, is_trunc n (P aa)] (H : Πa, P (tr a))
    : P aa :=
  trunc.rec H aa
end trunc

constant quotient.{u v} {A : Type.{u}} (R : A → A → Type.{v}) : Type.{max u v}

namespace quotient

  constant class_of {A : Type} (R : A → A → Type) (a : A) : quotient R

  constant eq_of_rel {A : Type} (R : A → A → Type) ⦃a a' : A⦄ (H : R a a')
    : class_of R a = class_of R a'

  protected constant rec {A : Type} {R : A → A → Type} {P : quotient R → Type}
    (Pc : Π(a : A), P (class_of R a)) (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a =[eq_of_rel R H] Pc a')
    (x : quotient R) : P x

  protected definition rec_on [reducible] {A : Type} {R : A → A → Type} {P : quotient R → Type}
    (x : quotient R) (Pc : Π(a : A), P (class_of R a))
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a =[eq_of_rel R H] Pc a') : P x :=
  quotient.rec Pc Pp x

end quotient

init_hits -- Initialize builtin computational rules for trunc and quotient

namespace trunc
  definition rec_tr [reducible] {n : trunc_index} {A : Type} {P : trunc n A → Type}
    [Pt : Πaa, is_trunc n (P aa)] (H : Πa, P (tr a)) (a : A) : trunc.rec H (tr a) = H a :=
  idp
end trunc

namespace quotient
  definition rec_class_of {A : Type} {R : A → A → Type} {P : quotient R → Type}
    (Pc : Π(a : A), P (class_of R a)) (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a =[eq_of_rel R H] Pc a')
    (a : A) : quotient.rec Pc Pp (class_of R a) = Pc a :=
  idp

  constant rec_eq_of_rel {A : Type} {R : A → A → Type} {P : quotient R → Type}
    (Pc : Π(a : A), P (class_of R a)) (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a =[eq_of_rel R H] Pc a')
    {a a' : A} (H : R a a') : apdo (quotient.rec Pc Pp) (eq_of_rel R H) = Pp H
end quotient

attribute quotient.class_of trunc.tr [constructor]
attribute quotient.rec trunc.rec [unfold 6]
attribute quotient.rec_on trunc.rec_on [unfold 4]
