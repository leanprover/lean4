/-!
This uses `simp -underLambda` to perform a calculation that involves well-founded
recursion and is thus hard to do with `decide`. It needs the `-underLambda` flag
as otherwise the well-founded function's equation lemmas cause it to loop.
-/

def find (P : Nat → Prop) [DecidablePred P] (i : Nat) (h : ∃ n, i ≤ n ∧ P n) : Nat :=
  if hi : P i then
    i
  else
    find P (i+1) (by
      obtain ⟨w, hle, h⟩ := h
      have : w ≠ i := fun heq => by cases heq; contradiction
      exact ⟨w, by omega, h⟩;
     )
decreasing_by sorry

-- Without -underLambda, the following example will unroll the `find` equation
-- very very often

/--
error: tactic 'fail' failed
P : Nat → Bool
h0 : ∀ (i : Nat), i < 10 → ¬P i = true
h1 : P 100 = true
⊢ (if hi : P 10 = true then 10 else find (fun n => P n = true) (10 + 1) ⋯) = 100
-/
#guard_msgs in
example (P : Nat → Bool) (h0 : ∀ i, i < 10 → ¬ P i) (h1 : P 100) :
    find (fun n => P n) 0 ⟨100, by omega, h1⟩ = 100 := by
  simp -underLambda [find, *]
  fail
