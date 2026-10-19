import Std.Tactic.BVDecide

/-!
Tests that the EPR pass of `bv_normalize` replaces ground facts by their `BitVec` encoding and removes
quantified facts from the hypotheses.
-/

open Std.Tactic.BVDecide.EPR.BitVec

example (α : Type) (a b : α) (P : α → Prop) (h1 : ∀ x, P x) (h2 : ¬P a) (h3 : a ≠ b)
    (h4 : True → P b) : False := by
  bv_normalize +epr
  trace_state
  sorry
