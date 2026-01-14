import Lean

-- This worked before issue #2361
example {α : Type} {P : α → Prop} (a : α) (h : P a) : ∃ x, P x := by
  constructor
  assumption

example {α : Type} {P : α → Prop} (a : α) (h : P a) : ∃ x, P x := by
  refine ⟨?m, ?c⟩
  -- `?m` is synthetic opaque, so `assumption` needs to be able to assign such metavariables
  -- for this to succeed.
  case c => assumption

example {α : Type} {P : α → Prop} (a : α) (h : P a) : ∃ x, P x := by
  refine' ⟨_, ?c⟩
  case c => assumption
