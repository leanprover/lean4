/-!
# Tests exercising basic behaviour of `rw`.

See also `tests/lean/run/rewrite.lean`.
-/

axiom appendNil {α} (as : List α) : as ++ [] = as
axiom appendAssoc {α} (as bs cs : List α) : (as ++ bs) ++ cs = as ++ (bs ++ cs)
axiom reverseEq {α} (as : List α) : as.reverse.reverse = as

theorem ex1 {α} (as bs : List α) : as.reverse.reverse ++ [] ++ [] ++ bs ++ bs = as ++ (bs ++ bs) := by
  rw [appendNil, appendNil, reverseEq];
  trace_state;
  rw [←appendAssoc];


theorem ex2 {α} (as bs : List α) : as.reverse.reverse ++ [] ++ [] ++ bs ++ bs = as ++ (bs ++ bs) := by
rewrite [reverseEq, reverseEq]; -- Error on second reverseEq
done

axiom zeroAdd (x : Nat) : 0 + x = x

theorem ex2a (x y z) (h₁ : 0 + x = y) (h₂ : 0 + y = z) : x = z := by
rewrite [zeroAdd] at h₁ h₂;
trace_state;
subst x;
subst y;
exact rfl

theorem ex3 (x y z) (h₁ : 0 + x = y) (h₂ : 0 + y = z) : x = z := by
rewrite [zeroAdd] at *;
subst x;
subst y;
exact rfl

theorem ex4 (x y z) (h₁ : 0 + x = y) (h₂ : 0 + y = z) : x = z := by
rewrite [appendAssoc] at *; -- Error
done

theorem ex5 (m n k : Nat) (h : 0 + n = m) (h : k = m) : k = n := by
rw [zeroAdd] at *;
trace_state; -- `h` is still a name for `h : k = m`
refine Eq.trans h ?hole;
apply Eq.symm;
assumption

theorem ex6 (p q r : Prop) (h₁ : q → r) (h₂ : p ↔ q) (h₃ : p) : r := by
rw [←h₂] at h₁;
exact h₁ h₃

theorem ex7 (p q r : Prop) (h₁ : q → r) (h₂ : p ↔ q) (h₃ : p) : r := by
rw [h₂] at h₃;
exact h₁ h₃

example (α : Type) (p : Prop) (a b c : α) (h : p → a = b) : a = c := by
  rw [h _]  -- should manifest goal `⊢ p`, like `rw [h]` would

/-!
Testing the `occs` configuration argument.
-/

variable (f : Nat → Nat) (w : ∀ n, f n = 0)

example : [f 1, f 2, f 1, f 2] = [0, 0, 0, 0] := by
  rw (config := {occs := .pos [2]}) [w]
  trace_state -- make sure we rewrote the first `f 2`, rather than the second `f 1`.
  rw [w, w]

example : [f 1, f 2, f 1, f 2] = [0, 0, 0, 0] := by
  rw (config := {occs := .all}) [w]
  trace_state -- expecting [0, f 2, 0, f 2] = [0, 0, 0, 0]
  rw [w]

example : [f 1, f 2, f 1, f 2] = [0, 0, 0, 0] := by
  rw (config := {occs := .pos [1, 2]}) [w]
  trace_state -- expecting [0, f 2, 0, f 2] = [0, 0, 0, 0]
  -- After the first rewrite, the argument of `w` have been instantiated as `1`,
  -- so the second eligible rewrite is the second `f 1`.
  rw [w]

example : [f 1, f 2, f 1, f 2] = [0, 0, 0, 0] := by
  rw (config := {occs := .neg [1]}) [w]
  trace_state -- expecting [f 1, 0, f 1, 0] = [0, 0, 0, 0]
  rw [w]

example : [f 1, f 2, f 1, f 2] = [0, 0, 0, 0] := by
  rw (config := {occs := .neg [1, 2]}) [w]
  trace_state -- expecting [f 1, f 2, 0, f 2] = [0, 0, 0, 0]
  rw [w, w]

example : [f 1, f 2, f 1, f 2] = [0, 0, 0, 0] := by
  rw (config := {occs := .neg [1, 3]}) [w]
  trace_state -- expecting [f 1, 0, f 1, f 2] = [0, 0, 0, 0]
  -- This one is slightly confusing:
  -- We skipped the first `f 1`, because `1 ∈ [1,3]`.
  -- We then rewrite the first `f 2 = 0`, because it is the second match.
  -- Now the second `f 1` is no longer eligible, because we have instantiated the argument of `w` to `2`.
  -- Finally we skip the second `f 2` because of `3 ∈ [1,3]`.
  rw [w, w]

-- A slightly trickier example, where there are already metavariables in the goal,
-- and we ensure that we don't unify metavariables in positions skipped by `occs`.
example : { x : Nat × Nat // x.1 = 0 ∧ x.2 = 0 } := by
  refine ⟨(f ?_, f ?_), ?_⟩
  rotate_right
  dsimp
  rw (config := {occs := .pos [2]}) [w]
  -- TODO: note that `rw` duplicates goals when there are metavariables.
  -- This should be fixed.
  rw [w]
  exact ⟨rfl, rfl⟩
  exact 37
  exact 0
