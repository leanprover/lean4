namespace Ex1

theorem elim_with_implicit_target (motive : Nat → Nat → Prop) (case1  : ∀ m n, motive m n) (n : Nat) {m : Nat} : motive m n := case1 _ _

example (n m : Nat) : n ≤ m := by
  induction n using elim_with_implicit_target
  case case1 => sorry

end Ex1

namespace Ex2

theorem elim_with_implicit_target (motive : Nat → Nat → Prop) (case1  : ∀ m n, motive m n) {n : Nat} (m : Nat) : motive m n := case1 _ _

example (n m : Nat) : n ≤ m := by
  induction m using elim_with_implicit_target
  case case1 => sorry

end Ex2

namespace Ex3

-- this one should work
theorem elim_with_implicit_target (motive : (n : Nat) → Fin n → Prop) (case1  : ∀ m n, motive m n) {n : Nat} (m : Fin n) : motive n m := case1 _ _

example (n : Nat) (m : Fin n) : n ≤ m := by
  induction m using elim_with_implicit_target
  case case1 => sorry

end Ex3
