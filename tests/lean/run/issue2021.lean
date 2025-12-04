prelude -- optional
import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
namespace Nat'

protected def modCore (y : Nat) : Nat → Nat → Nat
  | Nat.zero, x => x
  | Nat.succ fuel, x => if 0 < y ∧ y ≤ x then Nat'.modCore y fuel (x - y) else x

protected def mod' (x y : @& Nat) : Nat :=
Nat'.modCore y x x

@[simp] theorem zero_mod' (b : Nat) : Nat'.mod' 0 b = 0 := rfl

end Nat'

namespace Nat

private def gcdF' (x : Nat) : (∀ x₁, x₁ < x → Nat → Nat) → Nat → Nat :=
  match x with
  | 0      => fun _ y => y
  | succ x => fun f y => f (Nat'.mod' y (succ x)) sorry (succ x)

noncomputable def gcd' (a b : Nat) : Nat :=
  WellFounded.fix (measure id).wf gcdF' a b

@[simp] theorem gcd'_zero_left (y : Nat) : gcd' 0 y = y :=
  rfl

theorem gcd'_succ (x y : Nat) : gcd' (succ x) y = gcd' (Nat'.mod' y (succ x)) (succ x) :=
  rfl   -- replace with `id rfl` and everything is ok

/--
error: (kernel) application type mismatch
  @Eq.ndrec Nat (n✝ + 1) (fun n => gcd' n 0 = n) (of_eq_true (eq_self (n✝ + 1)))
argument has type
  n✝ + 1 = n✝ + 1
but function has type
  (fun n => gcd' n 0 = n) (n✝ + 1) → ∀ {b : Nat}, n✝ + 1 = b → (fun n => gcd' n 0 = n) b
-/
#guard_msgs in
@[simp] theorem gcd'_zero_right (n : Nat) : gcd' n 0 = n := by
  cases n <;> simp [gcd'_succ]

end Nat
