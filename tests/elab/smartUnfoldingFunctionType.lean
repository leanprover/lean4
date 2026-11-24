module

/-!
Smart unfolding must reduce marked matches in both the domain and the codomain of a
function type. When the match is stuck, unfolding must leave the recursive call folded.
-/

private def domain : Nat → Type
  | 0 => Nat
  | n+1 => (match n with | 0 => Nat | k+1 => domain k) → Unit

example (n : Nat) : domain (n+1) = ((match n with | 0 => Nat | k+1 => domain k) → Unit) := by
  fail_if_success exact rfl
  cases n <;> rfl

example (P : Type → Prop) (k : Nat) (h : P (domain k → Unit)) : P (domain (k+2)) := by
  dsimp (config := { autoUnfold := true }) only
  guard_target =ₛ P (domain k → Unit)
  exact h

private def codomain : Nat → Type
  | 0 => Nat
  | n+1 => (i : Nat) → (j : Fin i) → (match n with | 0 => Fin j.val | k+1 => codomain k)

example (n : Nat) :
    codomain (n+1) = ((i : Nat) → (j : Fin i) → (match n with | 0 => Fin j.val | k+1 => codomain k)) := by
  fail_if_success exact rfl
  cases n <;> rfl

example (P : Type → Prop) (h : P ((i : Nat) → (j : Fin i) → Fin j.val)) : P (codomain 1) := by
  dsimp (config := { autoUnfold := true }) only
  guard_target =ₛ P ((i : Nat) → (j : Fin i) → Fin j.val)
  exact h
