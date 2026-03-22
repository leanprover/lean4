/-!
# Delayed assignments record defeq constraint in type for elaborator

https://github.com/leanprover/lean4/issues/8488
-/

set_option warn.sorry false

/-!
The `clear_value` tactic should fail here because `?mv` depends on the *value* of `v`.
-/
/--
error: Tactic `clear_value` failed, the value of `v` cannot be cleared.
n : Nat
v : Nat := n + 1
⊢ 0 = (fun k => ?mv) 0 * 0
-/
#guard_msgs in
example (n : Nat) : True := by
  have : 0 = (fun k : Nat => let v := n + 1; ?mv) 0 * 0 := by
    extract_lets v
    clear_value v
  all_goals sorry

/-!
Succeeds when it is a `have`.
-/
example (n : Nat) : True := by
  have : 0 = (fun k : Nat => have v := n + 1; ?mv) 0 * 0 := by
    extract_lets v
    clear_value v
    sorry
  all_goals sorry

/-!
The `rw` tactic should fail here because the `?mv` argument depends on the value being `n + 1`.
-/
/--
error: Tactic `rewrite` failed: motive is not type correct:
  fun _a => 0 = (fun k => ?mv) 0 * 0
Error: Application value mismatch: In the application
  ?mv
the argument
  _a
is not definitionally equal to
  n + 1

Explanation: The rewrite tactic rewrites an expression 'e' using an equality 'a = b' by the following process. First, it looks for all 'a' in 'e'. Second, it tries to abstract these occurrences of 'a' to create a function 'm := fun _a => ...', called the *motive*, with the property that 'm a' is definitionally equal to 'e'. Third, we observe that 'congrArg' implies that 'm a = m b', which can be used with lemmas such as 'Eq.mpr' to change the goal. However, if 'e' depends on specific properties of 'a', then the motive 'm' might not typecheck.

Possible solutions: use rewrite's 'occs' configuration option to limit which occurrences are rewritten, or use 'simp' or 'conv' mode, which have strategies for certain kinds of dependencies (these tactics can handle proofs and 'Decidable' instances whose types depend on the rewritten term, and 'simp' can apply user-defined '@[congr]' theorems as well).

n : Nat
⊢ 0 = (fun k => ?m.17 k (n + 1)) 0 * 0
-/
#guard_msgs in
example (n : Nat) : True := by
  have : 0 = (fun k : Nat => let v := n + 1; ?mv) 0 * 0 := by
    extract_lets v
    subst v
    rw [Nat.add_comm n 1]
  all_goals sorry

/-!
Succeeds when it is a `have`.
-/
example (n : Nat) : True := by
  have : 0 = (fun k : Nat => have v := n + 1; ?mv) 0 * 0 := by
    extract_lets v
    subst v
    rw [Nat.add_comm n 1]
    sorry
  all_goals sorry

/-!
The `simp` tactic correctly makes no progress here.
Congruence lemma generation knows to make `defeqParam` parameters fixed.
-/
/-- error: `simp` made no progress -/
#guard_msgs in
example (n : Nat) : True := by
  have : 0 = (fun k : Nat => let v := n + 1; ?mv) 0 * 0 := by
    extract_lets v
    subst v
    dsimp only
    simp only [Nat.add_comm n 1]
  all_goals sorry
