def works (l : List α) : List α :=
  match l with
  | [] => []
  | _::tail =>
    works tail
decreasing_by decreasing_tactic -- to force well-founded recursion

-- Both of these appear in mathlib

@[simp]
theorem add_zero (n : Nat) : n + 0 = n := by sorry

@[simp]
theorem lt_add_iff_pos_left (a : Nat) {b : Nat} :
  a < b + a ↔ 0 < b
  := by sorry

-- Breaking this:

def should_still_work (l : List α) : List α :=
  match l with
  | [] => []
  | _::tail =>
    should_still_work tail
decreasing_by decreasing_tactic
