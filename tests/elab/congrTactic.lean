/-!
# Tests of the `congr` tactic
-/

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

example (h₁ : α = β) (h₂ : α = γ) (a : α) : cast h₁ a ≍ cast h₂ a := by
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

namespace Tao1
/-!
Reported on Zulip: https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/congr.20unexpectedly.20fails.20with.20Set.2Eimage/near/527382064

The `congr` tactic used to make no progress here because `congr` was computing the arity from the head function
(`Set.image`) rather than from the actual number of supplied arguments.
-/

def Set (α : Type _) := α → Prop
def Set.image {α β : Type _} (f : α → β) (s : Set α) : Set β :=
  fun y => ∃ x, s x ∧ f x = y
infixl:80 " '' " => Set.image

example {X Y : Type} (f : X → Y) (E F : Set X) (h : E = F) : f '' E = f '' F := by
  congr

/-!
This also didn't work, for the same reason.
-/
example {X Y : Type} (f g : X → Y) (h : f = g) : Set.image f = Set.image g := by
  congr

/-!
The `HEq` version also did not work.
-/
example {X Y Y' : Type} (h : Y = Y') (f : X → Y) (f' : X → Y') (hf : f ≍ f') (E : Set X) : f '' E ≍ f' '' E := by
  congr

end Tao1
