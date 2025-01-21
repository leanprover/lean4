import Lean

open Lean Meta Elab Tactic Grind in
elab "grind_test" : tactic => withMainContext do
  let declName := (← Term.getDeclName?).getD `_main
  Meta.Grind.preprocessAndProbe (← getMainGoal) declName do
    let nodes ← filterENodes fun e => return e.self.isAppOf ``HMul.hMul
    logInfo (nodes.toList.map (·.self))

set_option grind.debug true

class Semigroup (α : Type u) extends Mul α where
  mul_assoc (a b c : α) : a * b * c = a * (b * c)

export Semigroup (mul_assoc)

class MulComm (α : Type u)  extends Mul α where
  mul_comm (a b : α) : a * b = b * a

export MulComm (mul_comm)

class CommSemigroup (α : Type u) extends Semigroup α where
  mul_comm (a b : α) : a * b = b * a

instance [CommSemigroup α] : MulComm α where
  mul_comm := CommSemigroup.mul_comm

class One (α : Type u) where
  one : α

instance [One α] : OfNat α (nat_lit 1) where
  ofNat := One.one

class Monoid (α : Type u) extends Semigroup α, One α where
  one_mul (a : α) : 1 * a = a
  mul_one (a : α) : a * 1 = a

export Monoid (one_mul mul_one)

class CommMonoid (α : Type u) extends Monoid α where
  mul_comm (a b : α) : a * b = b * a

instance [CommMonoid α] : CommSemigroup α where
  mul_comm := CommMonoid.mul_comm

instance [CommMonoid α] : MulComm α where
  mul_comm := CommSemigroup.mul_comm

instance : CommMonoid Nat where
  mul := Nat.mul
  one := 1
  mul_assoc := Nat.mul_assoc
  mul_comm  := Nat.mul_comm
  one_mul   := Nat.one_mul
  mul_one   := Nat.mul_one

theorem left_comm [CommMonoid α] (a b c : α) : a * (b * c) = b * (a * c) := by
  rw [← Semigroup.mul_assoc, CommMonoid.mul_comm a b, Semigroup.mul_assoc]

/--
info: [b * c, a * (b * c), d * (b * c)]
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (a b c d : Nat) : b * (a * c) = d * (b * c) → False := by
  rw [left_comm] -- Introduces a new (non-canonical) instance for `Mul Nat`
  grind_test -- State should have only 3 `*`-applications
  sorry


set_option pp.notation false in
set_option pp.explicit true in
/--
info: [@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) b a, @HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) b d]
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (a b c d : Nat) : b * a = d * b → False := by
  rw [CommMonoid.mul_comm d b] -- Introduces a new (non-canonical) instance for `Mul Nat`
  -- See target here
  guard_target =ₛ
    @HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) b a
    =
    @HMul.hMul Nat Nat Nat (@instHMul Nat (@Semigroup.toMul Nat (@Monoid.toSemigroup Nat (@CommMonoid.toMonoid Nat instCommMonoidNat)))) b d
    → False
  grind_test -- State should have only 2 `*`-applications, and they use the same instance
  sorry
