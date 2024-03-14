-- Everything should be built-in, but we still need this import in order to use `config`.
-- Moving `Lean.Meta.Tactic.Congr!.Config` to `Init/MetaTypes.lean` and an update-stage0 should hopefully fix this?
import Lean.Meta.Tactic.Congr!

private axiom test_sorry : ∀ {α}, α
set_option autoImplicit true

namespace Tests

example (P : Prop) (h : P) : P := by convert h

example (α β : Type) (h : α = β) (b : β) : α := by
  convert b

example (α β : Type) (h : ∀ α β : Type, α = β) (b : β) : α := by
  convert b
  apply h

example (m n : Nat) (h : m = n) (b : Fin n) : Nat × Nat × Nat × Fin m := by
  convert (37, 57, 2, b)

example (α β : Type) (h : α = β) (b : β) : Nat × α := by
  -- type eq ok since arguments to `Prod` are explicit
  convert (37, b)

example (α β : Type) (h : β = α) (b : β) : Nat × α := by
  convert ← (37, b)

example (α β : Type) (h : α = β) (b : β) : Nat × Nat × Nat × α := by
  convert (37, 57, 2, b)

example (α β : Type) (h : α = β) (b : β) : Nat × Nat × Nat × α := by
  convert (37, 57, 2, b) using 2
  guard_target = (Nat × α) = (Nat × β)
  congr!

section convert_to

class AddCommMonoid (α) extends Add α where
  add_comm : ∀ x y : α, x + y = y + x

open AddCommMonoid

example {α} [AddCommMonoid α] {a b c d : α} (H : a = c) (H' : b = d) : a + b = d + c := by
  convert_to c + d = _ using 2
  rw [add_comm]

example {α} [AddCommMonoid α] {a b c d : α} (H : a = c) (H' : b = d) : a + b = d + c := by
  convert_to c + d = _ -- defaults to `using 1`
  congr 2
  rw [add_comm]

-- Check that `using 1` gives the same behavior as the default.
example {α} [AddCommMonoid α] {a b c d : α} (H : a = c) (H' : b = d) : a + b = d + c := by
  convert_to c + d = _ using 1
  congr 2
  rw [add_comm]

end convert_to

example (prime : Nat → Prop) (n : Nat) (h : prime (2 * n + 1)) :
    prime (n + n + 1) := by
  convert h
  · guard_target = (HAdd.hAdd : Nat → Nat → Nat) = HMul.hMul
    exact test_sorry
  · guard_target = n = 2
    exact test_sorry

example (prime : Nat → Prop) (n : Nat) (h : prime (2 * n + 1)) :
    prime (n + n + 1) := by
  convert (config := .unfoldSameFun) h
  guard_target = n + n = 2 * n
  exact test_sorry

example (p q : Nat → Prop) (h : ∀ ε > 0, p ε) :
    ∀ ε > 0, q ε := by
  convert h using 2 with ε hε
  guard_hyp hε : ε > 0
  guard_target = q ε ↔ p ε
  exact test_sorry

class Fintype (α : Type _) where
  card : Nat

axiom Fintype.foo (α : Type _) [Fintype α] : Fintype.card α = 2

axiom Fintype.foo' (α : Type _) [Fintype α] [Fintype (Option α)] : Fintype.card α = 2

axiom instFintypeBool : Fintype Bool

/- Would be "failed to synthesize instance Fintype ?m" without allowing TC failure. -/
example : @Fintype.card Bool instFintypeBool = 2 := by
  convert Fintype.foo _

example : @Fintype.card Bool instFintypeBool = 2 := by
  convert Fintype.foo' _ using 1
  guard_target = Fintype (Option Bool)
  exact test_sorry

example : True := by
  convert_to ?x + ?y = ?z
  case x => exact 1
  case y => exact 2
  case z => exact 3
  all_goals try infer_instance
  · simp
  · simp

example [Fintype α] [Fintype β] : Fintype.card α = Fintype.card β := by
  congr!
  guard_target = Fintype.card α = Fintype.card β
  congr! (config := {typeEqs := true})
  · guard_target = α = β
    exact test_sorry
  · rename_i inst1 inst2 h
    guard_target = HEq inst1 inst2
    have : Subsingleton (Fintype α) := test_sorry
    congr!
