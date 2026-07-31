/-!
A stuck abort raised by `isDefEqOnFailure` must not pre-empt the late special cases.

`isDefEqAppFallback` runs `isDefEqOnFailure` first, because `isDefEqProjInst` and friends unfold
the class projections that `getStuckMVar?` needs to see an unsynthesized instance in an argument
position. But "stuck on an instance" is not a verdict: one of the late special cases may close the
comparison without ever learning that instance. So the abort is held back and re-raised only if
they all decline.

Here, synthesizing the `CoeFun` instance for `h b` requires `Sem (T α k (opStar α k))`, which
`instSem` provides only as `Sem (T α k (opMul α k))`. Reconciling the two comes down to
`x * y =?= Mul.mul x y`, which `isDefEqProjInst` settles by unfolding `instHMul`. But `α` and its
`K α` instance are still metavariables at that point, so `isDefEqOnFailure` gets stuck on the
instance first. Aborting there loses a comparison that was about to succeed, and elaboration fails
with `h` never being coerced to a function.

Reduced from `Mathlib/RingTheory/Polynomial/UniversalFactorizationRing.lean`, where the same
`x1 * x2 =?= Mul.mul x1 x2` comparison is rescued and the stuck instance is `CommSemiring ?α`.
`backward.isDefEq.appOnFailure := true` selects the old, aborting behavior, asserted below as the
contrast.
-/

/-- Stands in for `CommSemiring`: supplies `Mul` through a parent projection. -/
class K (α : Type) extends Mul α where

class Op (α : Type) where
  f : α → α → α

/-- Two definitionally equal spellings of the same `Op α`, as in the `Module R R` diamond. -/
@[reducible] def opStar (α : Type) [K α] : Op α := ⟨fun x y => x * y⟩
@[reducible] def opMul  (α : Type) [K α] : Op α := ⟨fun x y => Mul.mul x y⟩

/-- Carries an `Op α` instance argument, like `M ⊗[R] N` carries `Module R R`. -/
structure T (α : Type) (k : K α) [Op α] where
  val : α

class Sem (X : Type)
instance instSem (α : Type) (k : K α) : Sem (@T α k (@opMul α k)) := ⟨⟩

structure Box (α : Type) (k : K α)
structure Hom (α : Type) (k : K α) where run : Box α k → Nat

instance instCoeFunHom (α : Type) (k : K α) [Sem (@T α k (@opStar α k))] :
    CoeFun (Hom α k) (fun _ => Box α k → Nat) := ⟨Hom.run⟩

def h {α : Type} {k : K α} : Hom α k := ⟨fun _ => 0⟩

@[reducible] def kNat : K Nat where
  mul a _ := a

-- The deferral lets `isDefEqProjInst` close the comparison, so the `CoeFun` instance is found.
example (b : Box Nat kNat) : Nat := h b

/--
error: Function expected at
  h
but this term has type
  Hom ?m.1 ?m.2

Note: Expected a function because this term is being applied to the argument
  b
-/
#guard_msgs in
set_option backward.isDefEq.appOnFailure true in
example (b : Box Nat kNat) : Nat := h b
