import Lean
/-!
Previously, unification wouldn't be very careful with the `isDefEq` cache for terms containing metavariables.
- This is mostly problematic because erasing the cache leads to exponential slowdowns (`test1` & `test2`)
- but in some cases it leads to metavariable assignments leaking into places where they shouldn't be,
  which either causes unification to fail where it should succeed (`test3`)
  or to succeed where it is expected to fail.

-/
set_option maxHeartbeats 1000

namespace test1
class A (n : Nat) where
  x : Nat

instance [A n] : A (n+1) where
  x := A.x n

theorem test [A 0] : A.x 100 = sorry := sorry

-- Previously, this example was exponentially slow
example [A 1] : A.x 100 = sorry := by
  fail_if_success rw [@test]
  sorry
end test1


namespace test2
@[irreducible] def A : Type := Unit

@[irreducible] def B : Type := Unit

unseal B in
@[coe] def AtoB (_a : A) : B := ()

instance : Coe A B where coe := AtoB

def h {α : Type} (a b : α) : Nat → α
| 0 => a
| n + 1 => h b a n

def f {α : Type} (a b : α) : Nat → Prop
| 0 => a = b
| n + 1 => f (h a b n) (h b a n) n ∧ f (h a a n) (h b b n) n

axiom foo {p} {α : Type} (a b : α) : f a b p

variable (x : A) (y : B)
-- Previously, this check was exponentially slow; now it is quadratically slow
#check (foo (↑x) y : f (AtoB x) y 30)
end test2


namespace test3
structure A (α : Type) where
  x : Type
  y : α

structure B (α : Type) extends A α where
  z : Nat

def A.map {α β} (f : α → β) (a : A α) : A β := ⟨a.x, f a.y⟩

open Lean Meta in
elab "unfold_head" e:term : term => do
  let e ← Elab.Term.elabTerm e none
  unfoldDefinition e

-- we use `unfold_head` in order to get the raw kernel projection `·.1` instead of the projection funtcion `A.x`.
def test {α} (i : B α) : unfold_head i.toA.x := sorry

-- Previously, in this example the unification failed,
-- because some metavariable assignment wasn't reverted properly
-- However, it is clearly the case that `(i.toA.map f).x` is the same as `i.toA.x`
example (i : B α) (f : α → β) : (i.toA.map f).x := by
  apply @test
end test3
