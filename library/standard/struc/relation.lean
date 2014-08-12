----------------------------------------------------------------------------------------------------
-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jeremy Avigad
----------------------------------------------------------------------------------------------------

import logic.connectives.prop

-- General properties of relations
-- -------------------------------

namespace relation

abbreviation reflexive {T : Type} (R : T → T → Type) : Type := ∀x, R x x
abbreviation symmetric {T : Type} (R : T → T → Type) : Type := ∀x y, R x y → R y x
abbreviation transitive {T : Type} (R : T → T → Type) : Type := ∀x y z, R x y → R y z → R x z

namespace is_reflexive

inductive class {T : Type} (R : T → T → Type)  : Prop :=
| mk : reflexive R → class R

abbreviation app ⦃T : Type⦄ {R : T → T → Type} (C : class R) : reflexive R
:= class_rec (λu, u) C

abbreviation infer ⦃T : Type⦄ {R : T → T → Type} {C : class R} : reflexive R
:= class_rec (λu, u) C

end is_reflexive

namespace is_symmetric

inductive class {T : Type} (R : T → T → Type)  : Prop :=
| mk : symmetric R → class R

abbreviation app ⦃T : Type⦄ {R : T → T → Type} (C : class R) ⦃x y : T⦄ (H : R x y) : R y x
:= class_rec (λu, u) C x y H

abbreviation infer ⦃T : Type⦄ {R : T → T → Type} {C : class R} ⦃x y : T⦄ (H : R x y) : R y x
:= class_rec (λu, u) C x y H

end is_symmetric

namespace is_transitive

inductive class {T : Type} (R : T → T → Type)  : Prop :=
| mk : transitive R → class R

abbreviation app ⦃T : Type⦄ {R : T → T → Type} (C : class R) ⦃x y z : T⦄ (H1 : R x y)
  (H2 : R y z) : R x z
:= class_rec (λu, u) C x y z H1 H2

abbreviation infer ⦃T : Type⦄ {R : T → T → Type} {C : class R} ⦃x y z : T⦄ (H1 : R x y)
  (H2 : R y z) : R x z
:= class_rec (λu, u) C x y z H1 H2

end is_transitive


-- Congruence for unary and binary functions
-- -----------------------------------------

namespace congr

inductive class {T1 : Type} (R1 : T1 → T1 → Prop) {T2 : Type} (R2 : T2 → T2 → Prop)
    (f : T1 → T2) : Prop :=
| mk : (∀x y, R1 x y → R2 (f x) (f y)) → class R1 R2 f

abbreviation app {T1 : Type} {R1 : T1 → T1 → Prop} {T2 : Type} {R2 : T2 → T2 → Prop}
    {f : T1 → T2} (C : class R1 R2 f) ⦃x y : T1⦄ : R1 x y → R2 (f x) (f y) :=
class_rec (λu, u) C x y

theorem infer {T1 : Type} (R1 : T1 → T1 → Prop) {T2 : Type} (R2 : T2 → T2 → Prop)
    (f : T1 → T2) {C : class R1 R2 f} ⦃x y : T1⦄ : R1 x y → R2 (f x) (f y) :=
class_rec (λu, u) C x y

-- for binary functions
inductive class2 {T1 : Type}  (R1 : T1 → T1 → Prop) {T2 : Type} (R2 : T2 → T2 → Prop)
    {T3 : Type} (R3 : T3 → T3 → Prop) (f : T1 → T2 → T3) : Prop :=
| mk2 : (∀(x1 y1 : T1) (x2 y2 : T2), R1 x1 y1 → R2 x2 y2 → R3 (f x1 x2) (f y1 y2)) →
    class2 R1 R2 R3 f

abbreviation app2 {T1 : Type} {R1 : T1 → T1 → Prop} {T2 : Type} {R2 : T2 → T2 → Prop}
    {T3 : Type} {R3 : T3 → T3 → Prop}
    {f : T1 → T2 → T3} (C : class2 R1 R2 R3 f) ⦃x1 y1 : T1⦄ ⦃x2 y2 : T2⦄
  : R1 x1 y1 → R2 x2 y2 → R3 (f x1 x2) (f y1 y2) :=
class2_rec (λu, u) C x1 y1 x2 y2

-- ### general tools to build instances

theorem compose
    {T2 : Type} {R2 : T2 → T2 → Prop}
    {T3 : Type} {R3 : T3 → T3 → Prop}
    {g : T2 → T3} (C2 : congr.class R2 R3 g)
    {{T1 : Type}} {R1 : T1 → T1 → Prop}
    {f : T1 → T2} (C1 : congr.class R1 R2 f) :
  congr.class R1 R3 (λx, g (f x)) :=
mk (λx1 x2 H, app C2 (app C1 H))

theorem compose21
    {T2 : Type} {R2 : T2 → T2 → Prop}
    {T3 : Type} {R3 : T3 → T3 → Prop}
    {T4 : Type} {R4 : T4 → T4 → Prop}
    {g : T2 → T3 → T4} (C3 : congr.class2 R2 R3 R4 g)
    ⦃T1 : Type⦄ {R1 : T1 → T1 → Prop}
    {f1 : T1 → T2} (C1 : congr.class R1 R2 f1)
    {f2 : T1 → T3} (C2 : congr.class R1 R3 f2) :
  congr.class R1 R4 (λx, g (f1 x) (f2 x)) :=
mk (λx1 x2 H, app2 C3 (app C1 H) (app C2 H))

theorem const {T2 : Type} (R2 : T2 → T2 → Prop) (H : relation.reflexive R2)
    ⦃T1 : Type⦄ (R1 : T1 → T1 → Prop) (c : T2) :
  class R1 R2 (λu : T1, c) :=
mk (λx y H1, H c)

end congr

end relation


-- TODO: notice these can't be in the congr namespace, if we want it visible without
-- using congr.

theorem congr_const [instance] {T2 : Type} (R2 : T2 → T2 → Prop)
    {C : relation.is_reflexive.class R2} ⦃T1 : Type⦄ (R1 : T1 → T1 → Prop) (c : T2) :
  relation.congr.class R1 R2 (λu : T1, c) :=
relation.congr.const R2 (relation.is_reflexive.app C) R1 c

theorem congr_trivial [instance] {T : Type} (R : T → T → Prop) :
  relation.congr.class R R (λu, u) :=
relation.congr.mk (λx y H, H)


-- Relations that can be coerced to functions / implications
-- ---------------------------------------------------------

namespace relation

namespace mp_like

inductive class {R : Type → Type → Prop} {a b : Type} (H : R a b) : Prop :=
| mk {} : (a → b) → @class R a b H

definition app {R : Type → Type → Prop} {a : Type} {b : Type} {H : R a b}
  (C : class H) : a → b := class_rec (λx, x) C

definition infer ⦃R : Type → Type → Prop⦄ {a : Type} {b : Type} (H : R a b)
  {C : class H} : a → b := class_rec (λx, x) C

end mp_like


-- Notation for operations on general symbols
-- ------------------------------------------

namespace operations

definition refl := is_reflexive.infer
definition symm := is_symmetric.infer
definition trans := is_transitive.infer
definition mp := mp_like.infer

end operations

namespace symbols

postfix `⁻¹`:100 := operations.symm
infixr `⬝`:75     := operations.trans

end symbols

end relation
