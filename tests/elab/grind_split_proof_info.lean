/-!
Tests the proofs that `grind` builds at case splits without instantiating them (see
`Grind.getProofInfo`): non-chronological backtracking and the declarations hoisted to case splits,
when subgoals are still open (interactive `cases_next`), and when the goal contains metavariables
created before `grind`.
-/

-- Subgoals remain open after `cases_next`, while facts proved for the other subgoals are hoisted to
-- the case split.
example (a b c : Nat) (h : a ≤ b) : min a c ≤ min b c := by
  grind =>
    instantiate only [= Nat.min_def]
    cases_next
    all_goals cases_next
    all_goals lia

example (a b c : Nat) (h : a ≤ b) : min a c ≤ min b c := by
  grind =>
    instantiate only [= Nat.min_def]
    repeat (first (lia) (cases_next))

example (a b c d : Int) (h : a ≤ b) (h' : c ≤ d) : min (min a c) d ≤ min (min b d) (d + 1) := by
  grind =>
    instantiate only [= Int.min_def]
    repeat (first (lia) (cases_next))

example (a b c d : Nat) (h : a ≤ b) (h' : c ≤ d) : min a c ≤ min b d := by
  grind =>
    instantiate only [= Nat.min_def]
    cases_next
    all_goals finish

-- The goal contains the metavariable `?y`.
example (x z : Int) (p : Prop) (h : x = 0 ∨ x = 1 ∨ x = 2) (h2 : p ∨ z ≥ x) (h3 : p → z ≥ 5) :
    ∃ y : Int, (x ≤ 2 ∧ z ≥ 0) ∨ y > x + z := by
  refine ⟨?y, ?_⟩
  rotate_left
  · grind
  · exact 0

example (x z : Int) (p : Prop) (h : x = 0 ∨ x = 1 ∨ x = 2) (h2 : p ∨ z ≥ x) (h3 : p → z ≥ 5) :
    ∃ y : Int, (x ≤ 2 ∧ z ≥ 0) ∨ y > x + z := by
  refine ⟨?y, ?_⟩
  rotate_left
  · grind =>
      repeat (first (lia) (cases_next))
  · exact 0

example (a b c : Int) (h : a ≤ b) : ∃ k : Int, min a c ≤ min b c ∨ k = a + 1 := by
  refine ⟨?k, ?_⟩
  rotate_left
  · grind =>
      instantiate only [= Int.min_def]
      repeat (first (lia) (cases_next))
  · exact 0
