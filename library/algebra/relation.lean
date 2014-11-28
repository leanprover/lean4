/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: algebra.relation
Author: Jeremy Avigad

General properties of relations, and classes for equivalence relations and congruences.
-/

import logic.prop

namespace relation

  section
    variables {T : Type} (R : T → T → Type)

    definition reflexive : Type := ∀x, R x x
    definition symmetric : Type := ∀⦃x y⦄, R x y → R y x
    definition transitive : Type := ∀⦃x y z⦄, R x y → R y z → R x z
  end

inductive is_reflexive [class] {T : Type} (R : T → T → Type) : Prop :=
mk : reflexive R → is_reflexive R

namespace is_reflexive

  definition app ⦃T : Type⦄ {R : T → T → Prop} (C : is_reflexive R) : reflexive R :=
  is_reflexive.rec (λu, u) C

  definition infer ⦃T : Type⦄ (R : T → T → Prop) [C : is_reflexive R] : reflexive R :=
  is_reflexive.rec (λu, u) C

end is_reflexive


inductive is_symmetric [class] {T : Type} (R : T → T → Type) : Prop :=
mk : symmetric R → is_symmetric R

namespace is_symmetric

  definition app ⦃T : Type⦄ {R : T → T → Prop} (C : is_symmetric R) : symmetric R :=
  is_symmetric.rec (λu, u) C

  definition infer ⦃T : Type⦄ (R : T → T → Prop) [C : is_symmetric R] : symmetric R :=
  is_symmetric.rec (λu, u) C

end is_symmetric


inductive is_transitive [class] {T : Type} (R : T → T → Type) : Prop :=
mk : transitive R → is_transitive R

namespace is_transitive

  definition app ⦃T : Type⦄ {R : T → T → Prop} (C : is_transitive R) : transitive R :=
  is_transitive.rec (λu, u) C

  definition infer ⦃T : Type⦄ (R : T → T → Prop) [C : is_transitive R] : transitive R :=
  is_transitive.rec (λu, u) C

end is_transitive


inductive is_equivalence [class] {T : Type} (R : T → T → Type) : Prop :=
mk : is_reflexive R → is_symmetric R → is_transitive R → is_equivalence R

theorem is_equivalence.is_reflexive [instance]
        {T : Type} (R : T → T → Type) {C : is_equivalence R} : is_reflexive R :=
is_equivalence.rec (λx y z, x) C

theorem is_equivalence.is_symmetric [instance]
        {T : Type} {R : T → T → Type} {C : is_equivalence R} : is_symmetric R :=
is_equivalence.rec (λx y z, y) C

theorem is_equivalence.is_transitive [instance]
       {T : Type} {R : T → T → Type} {C : is_equivalence R} : is_transitive R :=
is_equivalence.rec (λx y z, z) C

-- partial equivalence relation
inductive is_PER {T : Type} (R : T → T → Type) : Prop :=
mk : is_symmetric R → is_transitive R → is_PER R

theorem is_PER.is_symmetric [instance]
        {T : Type} {R : T → T → Type} {C : is_PER R} : is_symmetric R :=
is_PER.rec (λx y, x) C

theorem is_PER.is_transitive [instance]
        {T : Type} {R : T → T → Type} {C : is_PER R} : is_transitive R :=
  is_PER.rec (λx y, y) C

-- Congruence for unary and binary functions
-- -----------------------------------------

inductive congruence [class] {T1 : Type} (R1 : T1 → T1 → Prop) {T2 : Type} (R2 : T2 → T2 → Prop)
    (f : T1 → T2) : Prop :=
mk : (∀x y, R1 x y → R2 (f x) (f y)) → congruence R1 R2 f

-- for binary functions
inductive congruence2 [class] {T1 : Type}  (R1 : T1 → T1 → Prop) {T2 : Type} (R2 : T2 → T2 → Prop)
    {T3 : Type} (R3 : T3 → T3 → Prop) (f : T1 → T2 → T3) : Prop :=
mk : (∀(x1 y1 : T1) (x2 y2 : T2), R1 x1 y1 → R2 x2 y2 → R3 (f x1 x2) (f y1 y2)) →
    congruence2 R1 R2 R3 f

namespace congruence

  definition app {T1 : Type} {R1 : T1 → T1 → Prop} {T2 : Type} {R2 : T2 → T2 → Prop}
      {f : T1 → T2} (C : congruence R1 R2 f) ⦃x y : T1⦄ : R1 x y → R2 (f x) (f y) :=
  rec (λu, u) C x y

  theorem infer {T1 : Type} (R1 : T1 → T1 → Prop) {T2 : Type} (R2 : T2 → T2 → Prop)
      (f : T1 → T2) [C : congruence R1 R2 f] ⦃x y : T1⦄ : R1 x y → R2 (f x) (f y) :=
  rec (λu, u) C x y

  definition app2 {T1 : Type} {R1 : T1 → T1 → Prop} {T2 : Type} {R2 : T2 → T2 → Prop}
      {T3 : Type} {R3 : T3 → T3 → Prop}
      {f : T1 → T2 → T3} (C : congruence2 R1 R2 R3 f) ⦃x1 y1 : T1⦄ ⦃x2 y2 : T2⦄ :
    R1 x1 y1 → R2 x2 y2 → R3 (f x1 x2) (f y1 y2) :=
  congruence2.rec (λu, u) C x1 y1 x2 y2

-- ### general tools to build instances

  theorem compose
      {T2 : Type} {R2 : T2 → T2 → Prop}
      {T3 : Type} {R3 : T3 → T3 → Prop}
      {g : T2 → T3} (C2 : congruence R2 R3 g)
      ⦃T1 : Type⦄ {R1 : T1 → T1 → Prop}
      {f : T1 → T2} (C1 : congruence R1 R2 f) :
    congruence R1 R3 (λx, g (f x)) :=
  mk (λx1 x2 H, app C2 (app C1 H))

  theorem compose21
      {T2 : Type} {R2 : T2 → T2 → Prop}
      {T3 : Type} {R3 : T3 → T3 → Prop}
      {T4 : Type} {R4 : T4 → T4 → Prop}
      {g : T2 → T3 → T4} (C3 : congruence2 R2 R3 R4 g)
      ⦃T1 : Type⦄ {R1 : T1 → T1 → Prop}
      {f1 : T1 → T2} (C1 : congruence R1 R2 f1)
      {f2 : T1 → T3} (C2 : congruence R1 R3 f2) :
    congruence R1 R4 (λx, g (f1 x) (f2 x)) :=
  mk (λx1 x2 H, app2 C3 (app C1 H) (app C2 H))

  theorem const {T2 : Type} (R2 : T2 → T2 → Prop) (H : relation.reflexive R2)
      ⦃T1 : Type⦄ (R1 : T1 → T1 → Prop) (c : T2) :
    congruence R1 R2 (λu : T1, c) :=
  mk (λx y H1, H c)

end congruence

-- Notice these can't be in the congruence namespace, if we want it visible without
-- using congruence.

theorem congruence_const [instance] {T2 : Type} (R2 : T2 → T2 → Prop)
    [C : is_reflexive R2] ⦃T1 : Type⦄ (R1 : T1 → T1 → Prop) (c : T2) :
  congruence R1 R2 (λu : T1, c) :=
congruence.const R2 (is_reflexive.app C) R1 c

theorem congruence_trivial [instance] {T : Type} (R : T → T → Prop) :
  congruence R R (λu, u) :=
congruence.mk (λx y H, H)


-- Relations that can be coerced to functions / implications
-- ---------------------------------------------------------

inductive mp_like [class] {R : Type → Type → Prop} {a b : Type} (H : R a b) : Type :=
mk {} : (a → b) → mp_like H

namespace mp_like

  definition app.{l} {R : Type → Type → Prop} {a : Type} {b : Type} {H : R a b}
    (C : mp_like H) : a → b := rec (λx, x) C

  definition infer ⦃R : Type → Type → Prop⦄ {a : Type} {b : Type} (H : R a b)
    {C : mp_like H} : a → b := rec (λx, x) C

end mp_like


-- Notation for operations on general symbols
-- ------------------------------------------

-- e.g. if R is an instance of the class, then "refl R" is reflexivity for the class
definition rel_refl := is_reflexive.infer
definition rel_symm := is_symmetric.infer
definition rel_trans := is_transitive.infer
definition rel_mp := mp_like.infer

end relation
