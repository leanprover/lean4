-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jeremy Avigad

import logic.connectives.prop


-- General properties of relations
-- -------------------------------

namespace relation

abbreviation reflexive {T : Type} (R : T → T → Type) : Type := ∀x, R x x
abbreviation symmetric {T : Type} (R : T → T → Type) : Type := ∀⦃x y⦄, R x y → R y x
abbreviation transitive {T : Type} (R : T → T → Type) : Type := ∀⦃x y z⦄, R x y → R y z → R x z


inductive is_reflexive {T : Type} (R : T → T → Type) : Prop :=
| is_reflexive_mk : reflexive R → is_reflexive R

namespace is_reflexive

  abbreviation app ⦃T : Type⦄ {R : T → T → Type} (C : is_reflexive R) : reflexive R :=
  is_reflexive_rec (λu, u) C

  abbreviation infer ⦃T : Type⦄ (R : T → T → Type) {C : is_reflexive R} : reflexive R :=
  is_reflexive_rec (λu, u) C

end is_reflexive


inductive is_symmetric {T : Type} (R : T → T → Type) : Prop :=
| is_symmetric_mk : symmetric R → is_symmetric R

namespace is_symmetric

  abbreviation app ⦃T : Type⦄ {R : T → T → Type} (C : is_symmetric R) : symmetric R :=
  is_symmetric_rec (λu, u) C

  abbreviation infer ⦃T : Type⦄ (R : T → T → Type) {C : is_symmetric R} : symmetric R :=
  is_symmetric_rec (λu, u) C

end is_symmetric


inductive is_transitive {T : Type} (R : T → T → Type) : Prop :=
| is_transitive_mk : transitive R → is_transitive R

namespace is_transitive

  abbreviation app ⦃T : Type⦄ {R : T → T → Type} (C : is_transitive R) : transitive R :=
  is_transitive_rec (λu, u) C

  abbreviation infer ⦃T : Type⦄ (R : T → T → Type) {C : is_transitive R} : transitive R :=
  is_transitive_rec (λu, u) C

end is_transitive


inductive is_equivalence {T : Type} (R : T → T → Type) : Prop :=
| is_equivalence_mk : is_reflexive R → is_symmetric R → is_transitive R → is_equivalence R

namespace is_equivalence

  theorem is_reflexive {T : Type} (R : T → T → Type) {C : is_equivalence R} : is_reflexive R :=
  is_equivalence_rec (λx y z, x) C

  theorem is_symmetric {T : Type} {R : T → T → Type} {C : is_equivalence R} : is_symmetric R :=
  is_equivalence_rec (λx y z, y) C

  theorem is_transitive {T : Type} {R : T → T → Type} {C : is_equivalence R} : is_transitive R :=
  is_equivalence_rec (λx y z, z) C

end is_equivalence

instance is_equivalence.is_reflexive
instance is_equivalence.is_symmetric
instance is_equivalence.is_transitive


-- partial equivalence relation
inductive is_PER {T : Type} (R : T → T → Type) : Prop :=
| is_PER_mk : is_symmetric R → is_transitive R → is_PER R

namespace is_PER

  theorem is_symmetric {T : Type} {R : T → T → Type} {C : is_PER R} : is_symmetric R :=
  is_PER_rec (λx y, x) C

  theorem is_transitive {T : Type} {R : T → T → Type} {C : is_PER R} : is_transitive R :=
  is_PER_rec (λx y, y) C

end is_PER

instance is_PER.is_symmetric
instance is_PER.is_transitive


-- Congruence for unary and binary functions
-- -----------------------------------------

inductive congr {T1 : Type} (R1 : T1 → T1 → Prop) {T2 : Type} (R2 : T2 → T2 → Prop)
    (f : T1 → T2) : Prop :=
| congr_mk : (∀x y, R1 x y → R2 (f x) (f y)) → congr R1 R2 f

-- for binary functions
inductive congr2 {T1 : Type}  (R1 : T1 → T1 → Prop) {T2 : Type} (R2 : T2 → T2 → Prop)
    {T3 : Type} (R3 : T3 → T3 → Prop) (f : T1 → T2 → T3) : Prop :=
| congr2_mk : (∀(x1 y1 : T1) (x2 y2 : T2), R1 x1 y1 → R2 x2 y2 → R3 (f x1 x2) (f y1 y2)) →
    congr2 R1 R2 R3 f

namespace congr

  abbreviation app {T1 : Type} {R1 : T1 → T1 → Prop} {T2 : Type} {R2 : T2 → T2 → Prop}
      {f : T1 → T2} (C : congr R1 R2 f) ⦃x y : T1⦄ : R1 x y → R2 (f x) (f y) :=
  congr_rec (λu, u) C x y

  theorem infer {T1 : Type} (R1 : T1 → T1 → Prop) {T2 : Type} (R2 : T2 → T2 → Prop)
      (f : T1 → T2) {C : congr R1 R2 f} ⦃x y : T1⦄ : R1 x y → R2 (f x) (f y) :=
  congr_rec (λu, u) C x y

  abbreviation app2 {T1 : Type} {R1 : T1 → T1 → Prop} {T2 : Type} {R2 : T2 → T2 → Prop}
      {T3 : Type} {R3 : T3 → T3 → Prop}
      {f : T1 → T2 → T3} (C : congr2 R1 R2 R3 f) ⦃x1 y1 : T1⦄ ⦃x2 y2 : T2⦄ :
    R1 x1 y1 → R2 x2 y2 → R3 (f x1 x2) (f y1 y2) :=
  congr2_rec (λu, u) C x1 y1 x2 y2

-- ### general tools to build instances

  theorem compose
      {T2 : Type} {R2 : T2 → T2 → Prop}
      {T3 : Type} {R3 : T3 → T3 → Prop}
      {g : T2 → T3} (C2 : congr R2 R3 g)
      ⦃T1 : Type⦄ {R1 : T1 → T1 → Prop}
      {f : T1 → T2} (C1 : congr R1 R2 f) :
    congr R1 R3 (λx, g (f x)) :=
  congr_mk (λx1 x2 H, app C2 (app C1 H))

  theorem compose21
      {T2 : Type} {R2 : T2 → T2 → Prop}
      {T3 : Type} {R3 : T3 → T3 → Prop}
      {T4 : Type} {R4 : T4 → T4 → Prop}
      {g : T2 → T3 → T4} (C3 : congr2 R2 R3 R4 g)
      ⦃T1 : Type⦄ {R1 : T1 → T1 → Prop}
      {f1 : T1 → T2} (C1 : congr R1 R2 f1)
      {f2 : T1 → T3} (C2 : congr R1 R3 f2) :
    congr R1 R4 (λx, g (f1 x) (f2 x)) :=
  congr_mk (λx1 x2 H, app2 C3 (app C1 H) (app C2 H))

  theorem const {T2 : Type} (R2 : T2 → T2 → Prop) (H : relation.reflexive R2)
      ⦃T1 : Type⦄ (R1 : T1 → T1 → Prop) (c : T2) :
    congr R1 R2 (λu : T1, c) :=
  congr_mk (λx y H1, H c)

end congr

-- Notice these can't be in the congr namespace, if we want it visible without
-- using congr.

theorem congr_const [instance] {T2 : Type} (R2 : T2 → T2 → Prop)
    {C : is_reflexive R2} ⦃T1 : Type⦄ (R1 : T1 → T1 → Prop) (c : T2) :
  congr R1 R2 (λu : T1, c) :=
congr.const R2 (is_reflexive.app C) R1 c

theorem congr_trivial [instance] {T : Type} (R : T → T → Prop) :
  congr R R (λu, u) :=
congr_mk (λx y H, H)


-- Relations that can be coerced to functions / implications
-- ---------------------------------------------------------

inductive mp_like {R : Type → Type → Prop} {a b : Type} (H : R a b) : Prop :=
| mp_like_mk {} : (a → b) → @mp_like R a b H

namespace mp_like

  definition app {R : Type → Type → Prop} {a : Type} {b : Type} {H : R a b}
    (C : mp_like H) : a → b := mp_like_rec (λx, x) C

  definition infer ⦃R : Type → Type → Prop⦄ {a : Type} {b : Type} (H : R a b)
    {C : mp_like H} : a → b := mp_like_rec (λx, x) C

end mp_like


-- Notation for operations on general symbols
-- ------------------------------------------

-- e.g. if R is an instance of the class, then "refl R" is reflexivity for the class
definition rel_refl := is_reflexive.infer
definition rel_symm := is_symmetric.infer
definition rel_trans := is_transitive.infer
definition rel_mp := mp_like.infer

end relation
