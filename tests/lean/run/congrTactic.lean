example (h : a = b) : Nat.succ (a + 1) = Nat.succ (b + 1) := by
  congr

example (h : a = b) : Nat.succ (a + 1) = Nat.succ (b + 1) := by
  congr 1
  show a + 1 = b + 1
  rw [h]

def f (p : Prop) (a : Nat) (h : a > 0) [Decidable p] : Nat :=
  if p then
    a - 1
  else
    a + 1

example (h : a = b) : f True (a + 1) (by simp +arith) = f (0 = 0) (b + 1) (by simp +arith) := by
  congr
  decide

example (h : a = b) : f True (a + 1) (by simp +arith) = f (0 = 0) (b + 1) (by simp +arith) := by
  congr 1
  · decide
  · show a + 1 = b + 1
    rw [h]

example (h₁ : α = β) (h₂ : α = γ) (a : α) : HEq (cast h₁ a) (cast h₂ a) := by
  congr
  · subst h₁ h₂; rfl
  · subst h₁ h₂; apply heq_of_eq; rfl

example (f : Nat → Nat) (g : Nat → Nat) : f (g (x + y)) = f (g (y + x)) := by
  congr 2
  rw [Nat.add_comm]

example (p q r : Prop) (h : q = r) : (p → q) = (p → r) := by
  congr

example (p q r s : Prop) (h₁ : q = r) (h₂ : r = s) : (p → q) = (p → s) := by
  congr
  rw [h₁, h₂]
