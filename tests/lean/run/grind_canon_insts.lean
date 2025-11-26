module
public meta import Lean.Meta.Tactic.Grind
#exit -- TODO: reenable after we add support for running code in interactive mode
public section
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

open Lean Meta Elab Tactic Grind in
meta def fallback : Fallback := do
  let nodes ← filterENodes fun e => return e.self.isApp && e.self.isAppOf ``HMul.hMul
  trace[Meta.debug] "{nodes.map (·.self) |>.qsort Expr.lt}"
  (← get).mvarId.admit

set_option trace.Meta.debug true

/--
trace: [Meta.debug] [↑a * ↑b,
     ↑a * (↑b * ↑c),
     ↑b * ↑c,
     ↑d * (↑b * ↑c),
     -1 * (↑b * ↑c * ↑d),
     ↑a * ↑b * ↑c,
     ↑b * ↑c * ↑d,
     a * (b * c),
     b * c,
     d * (b * c)]
-/
#guard_msgs (trace) in
example (a b c d : Nat) : b * (a * c) = d * (b * c) → False := by
  rw [left_comm] -- Introduces a new (non-canonical) instance for `Mul Nat`
  grind on_failure fallback -- State should have only 3 `*`-applications
