/-!
Minimization of a problem noticed in Mathlib's slowest file `Mathlib.RingTheory.Kaehler`
(although this is probably not the cause of the major slowdown, it is still a problem).

Adding an irrelevant `variable` statement can dramatically slow down every elaboration problem.

In this example we have:
```
...

example : Nat := 0

variable [Algebra R S]

example : Nat := 0 -- now takes more than 9x as many heartbeats!
```
-/

universe u

section Mathlib.Init.Order.Defs

class LinearOrder (α : Type u) where

end Mathlib.Init.Order.Defs

section Mathlib.Algebra.Group.Defs

class SMul (M : Type u) (α : Type u) where

class Semigroup (G : Type u) extends Mul G where

class AddSemigroup (G : Type u) extends Add G where

class AddMonoid (M : Type u) extends AddSemigroup M where

class Monoid (M : Type u) extends Semigroup M where

class AddCommMonoid (M : Type u) extends AddMonoid M

class CommMonoid (M : Type u) extends Monoid M

class AddCommGroup (G : Type u)

end Mathlib.Algebra.Group.Defs

section Mathlib.Algebra.GroupWithZero.Defs

class SemigroupWithZero (S₀ : Type u) extends Semigroup S₀

end Mathlib.Algebra.GroupWithZero.Defs

section Mathlib.Algebra.Ring.Defs

variable {α : Type u}

class Distrib (R : Type u) extends Mul R where

class NonUnitalNonAssocSemiring (α : Type u) extends AddCommMonoid α, Distrib α

class NonUnitalSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, SemigroupWithZero α

class NonAssocSemiring (α : Type u) extends NonUnitalNonAssocSemiring α

class NonUnitalNonAssocRing (α : Type u) extends AddCommGroup α

class NonUnitalRing (α : Type u) extends NonUnitalNonAssocRing α, NonUnitalSemiring α

class Semiring (α : Type u) extends NonUnitalSemiring α

class Ring (R : Type u) extends Semiring R, AddCommGroup R

class NonUnitalNonAssocCommSemiring (α : Type u) extends NonUnitalNonAssocSemiring α

class NonUnitalCommSemiring (α : Type u) extends NonUnitalSemiring α

class CommSemiring (R : Type u) extends Semiring R, CommMonoid R

instance (priority := 100) CommSemiring.toNonUnitalCommSemiring [CommSemiring α] :
    NonUnitalCommSemiring α :=
  { inferInstanceAs (CommMonoid α), inferInstanceAs (CommSemiring α) with }

instance (priority := 200) [Ring α] : Semiring α :=
  { ‹Ring α› with }

class NonUnitalNonAssocCommRing (α : Type u)
  extends NonUnitalNonAssocCommSemiring α

class NonUnitalCommRing (α : Type u) extends NonUnitalRing α, NonUnitalNonAssocCommRing α

instance (priority := 100) NonUnitalCommRing.toNonUnitalCommSemiring [s : NonUnitalCommRing α] :
    NonUnitalCommSemiring α :=
  { s with }

class CommRing (α : Type u) extends Ring α, CommMonoid α

instance (priority := 100) CommRing.toCommSemiring [s : CommRing α] : CommSemiring α :=
  { s with }

instance (priority := 100) CommRing.toNonUnitalCommRing [s : CommRing α] : NonUnitalCommRing α :=
  { s with }

end Mathlib.Algebra.Ring.Defs

section Mathlib.Algebra.Order.Ring.Defs

class OrderedSemiring (α : Type u) extends Semiring α where
  protected zero_le_one : True

class OrderedCommSemiring (α : Type u) extends OrderedSemiring α, CommSemiring α where

class OrderedRing (α : Type u) extends Ring α where

class OrderedCommRing (α : Type u) extends OrderedRing α, CommRing α

class StrictOrderedSemiring (α : Type u) extends Semiring α where

class StrictOrderedCommSemiring (α : Type u) extends StrictOrderedSemiring α, CommSemiring α

class StrictOrderedRing (α : Type u) extends Ring α where

class LinearOrderedSemiring (α : Type u) extends StrictOrderedSemiring α

class LinearOrderedCommSemiring (α : Type u) extends StrictOrderedCommSemiring α,
  LinearOrderedSemiring α

class LinearOrderedRing (α : Type u) extends StrictOrderedRing α, LinearOrder α

class LinearOrderedCommRing (α : Type u) extends LinearOrderedRing α

end Mathlib.Algebra.Order.Ring.Defs

section Mathlib.Algebra.Algebra.Defs

class Algebra (R : Type) (A : Type) [Semigroup R] [Semigroup A] extends SMul R A where

end Mathlib.Algebra.Algebra.Defs

variable (R S : Type) [NonUnitalRing R] [NonUnitalRing S]

set_option maxHeartbeats 10 in
example : Nat := 0

variable [Algebra R S] -- Add this irrelevant variable, and we take about 15x more heartbeats.

/--
error: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (90) has been reached
use `set_option maxHeartbeats <num>` to set the limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
set_option maxHeartbeats 90 in
example : Nat := 0
