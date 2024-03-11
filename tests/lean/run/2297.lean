universe u v

-- This is a mock-up of the `HasLimitsOfSize` typeclass in mathlib4.
class HLOS.{a,b} (C : Type b) where
  P : Type a

-- We only have an instance when there is a "universe inequality".
instance HLOS_max : HLOS.{a} (Type max a b) := sorry

example : HLOS.{a} (Type max a b) := HLOS_max.{a, max a b} -- Success
example : HLOS.{a} (Type max a b) := inferInstance -- Previously failed with: stuck at max a b =?= max a ?u

-- In mathlib4 we currently make use of the following workaround:
abbrev TypeMax := Type max u v

instance (priority := high) HLOS_max' : HLOS.{a} (TypeMax.{a, b}) := sorry

example : HLOS.{a} (TypeMax.{a, b}) := HLOS_max'.{a} -- Success
example : HLOS.{a} (TypeMax.{a, b}) := inferInstance -- Success

example : Type max v u = TypeMax.{v} := rfl -- Previously failed with: `max u v =?= max v ?u`
example : Type max v u = TypeMax.{u} := rfl -- Previously failed with: `max u v =?= max u ?u`
