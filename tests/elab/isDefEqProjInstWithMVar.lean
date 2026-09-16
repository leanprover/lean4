/-!
Regression test:
`isDefEqApp` calls `isDefEqOnFailure`. If it is stuck on a metavariable during instance search,
a stuck exception is thrown before `isDefEqProjInst` was tried. This made comparisons like
`x * y =?= Mul.mul x y` wrongly fail at implicit transparency.

This was fixed by deferring throwing the stuck exception until heuristics such as `isDefEqProjInst`
was tried.
-/

/-- like `CommSemiring` -/
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

set_option backward.isDefEq.throwOnStuckAfterApp true in
/--
error: Function expected at
  h
but this term has type
  Hom ?m.1 ?m.2

Note: Expected a function because this term is being applied to the argument
  b
-/
/-
Reason:
`[implicit] HMul.hmul x y =?= Mul.mul x y`, involving a `Mul` mvar, fails.
`isDefEqApp` calls `isDefEqOnFailure`, which finds the mvar and throws a stuck exception.
Lean can't synthesize the mvar though, so we fail hard before trying `isDefEqProjInst`.

This was fixed by deferring the stuck exception until `isDefEqProjInst` was tried.
-/
#guard_msgs in
example (b : Box Nat kNat) : Nat := h b

-- succeeds now
example (b : Box Nat kNat) : Nat := h b
