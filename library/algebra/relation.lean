/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

General properties of relations, and classes for equivalence relations and congruences.
-/

namespace relation

/- properties of binary relations -/

section
  variables {T : Type} (R : T → T → Type)

  definition reflexive : Type := ∀x, R x x
  definition symmetric : Type := ∀⦃x y⦄, R x y → R y x
  definition transitive : Type := ∀⦃x y z⦄, R x y → R y z → R x z
end


/- classes for equivalence relations -/

structure is_reflexive [class] {T : Type} (R : T → T → Type) := (refl : reflexive R)
structure is_symmetric [class] {T : Type} (R : T → T → Type) := (symm : symmetric R)
structure is_transitive [class] {T : Type} (R : T → T → Type) := (trans : transitive R)

structure is_equivalence [class] {T : Type} (R : T → T → Type)
extends is_reflexive R, is_symmetric R, is_transitive R

-- partial equivalence relation
structure is_PER {T : Type} (R : T → T → Type) extends is_symmetric R, is_transitive R

-- Generic notation. For example, is_refl R is the reflexivity of R, if that can be
-- inferred by type class inference
section
  variables {T : Type} (R : T → T → Type)
  definition rel_refl [C : is_reflexive R] := is_reflexive.refl R
  definition rel_symm [C : is_symmetric R] := is_symmetric.symm R
  definition rel_trans [C : is_transitive R] := is_transitive.trans R
end


/- classes for unary and binary congruences with respect to arbitrary relations -/

structure is_congruence [class]
  {T1 : Type} (R1 : T1 → T1 → Prop)
  {T2 : Type} (R2 : T2 → T2 → Prop)
  (f : T1 → T2) :=
(congr : ∀{x y}, R1 x y → R2 (f x) (f y))

structure is_congruence2 [class]
  {T1 : Type} (R1 : T1 → T1 → Prop)
  {T2 : Type} (R2 : T2 → T2 → Prop)
  {T3 : Type} (R3 : T3 → T3 → Prop)
  (f : T1 → T2 → T3) :=
(congr2 : ∀{x1 y1 : T1} {x2 y2 : T2}, R1 x1 y1 → R2 x2 y2 → R3 (f x1 x2) (f y1 y2))

namespace is_congruence

  -- makes the type class explicit
  definition app {T1 : Type} {R1 : T1 → T1 → Prop} {T2 : Type} {R2 : T2 → T2 → Prop}
      {f : T1 → T2} (C : is_congruence R1 R2 f) ⦃x y : T1⦄ : R1 x y → R2 (f x) (f y) :=
  is_congruence.rec (λu, u) C x y

  definition app2 {T1 : Type} {R1 : T1 → T1 → Prop} {T2 : Type} {R2 : T2 → T2 → Prop}
      {T3 : Type} {R3 : T3 → T3 → Prop}
      {f : T1 → T2 → T3} (C : is_congruence2 R1 R2 R3 f) ⦃x1 y1 : T1⦄ ⦃x2 y2 : T2⦄ :
    R1 x1 y1 → R2 x2 y2 → R3 (f x1 x2) (f y1 y2) :=
  is_congruence2.rec (λu, u) C x1 y1 x2 y2

  /- tools to build instances -/

  definition compose
      {T2 : Type} {R2 : T2 → T2 → Prop}
      {T3 : Type} {R3 : T3 → T3 → Prop}
      {g : T2 → T3} (C2 : is_congruence R2 R3 g)
      ⦃T1 : Type⦄ {R1 : T1 → T1 → Prop}
      {f : T1 → T2} [C1 : is_congruence R1 R2 f] :
    is_congruence R1 R3 (λx, g (f x)) :=
  is_congruence.mk (λx1 x2 H, app C2 (app C1 H))

  definition compose21
      {T2 : Type} {R2 : T2 → T2 → Prop}
      {T3 : Type} {R3 : T3 → T3 → Prop}
      {T4 : Type} {R4 : T4 → T4 → Prop}
      {g : T2 → T3 → T4} (C3 : is_congruence2 R2 R3 R4 g)
      ⦃T1 : Type⦄ {R1 : T1 → T1 → Prop}
      {f1 : T1 → T2} [C1 : is_congruence R1 R2 f1]
      {f2 : T1 → T3} [C2 : is_congruence R1 R3 f2] :
    is_congruence R1 R4 (λx, g (f1 x) (f2 x)) :=
  is_congruence.mk (λx1 x2 H, app2 C3 (app C1 H) (app C2 H))

  definition const {T2 : Type} (R2 : T2 → T2 → Prop) (H : relation.reflexive R2)
      ⦃T1 : Type⦄ (R1 : T1 → T1 → Prop) (c : T2) :
    is_congruence R1 R2 (λu : T1, c) :=
  is_congruence.mk (λx y H1, H c)

end is_congruence

definition congruence_const [instance] {T2 : Type} (R2 : T2 → T2 → Prop)
    [C : is_reflexive R2] ⦃T1 : Type⦄ (R1 : T1 → T1 → Prop) (c : T2) :
  is_congruence R1 R2 (λu : T1, c) :=
is_congruence.const R2 (is_reflexive.refl R2) R1 c

definition congruence_trivial [instance] {T : Type} (R : T → T → Prop) :
  is_congruence R R (λu, u) :=
is_congruence.mk (λx y H, H)


/- relations that can be coerced to functions / implications-/

structure mp_like [class] (R : Type → Type → Type) :=
(app : Π{a b : Type}, R a b → (a → b))

definition rel_mp (R : Type → Type → Type) [C : mp_like R] {a b : Type} (H : R a b) :=
mp_like.app H


end relation
