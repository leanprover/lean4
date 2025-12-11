import Lean.Util.Reprove

-- Test successful reprove
theorem simpleTheorem : 1 + 1 = 2 := rfl

reprove simpleTheorem by rfl

theorem withTactics : ∀ n : Nat, n + 0 = n := by
  intro n
  rw [Nat.add_zero]

reprove withTactics by
  intro n
  simp

reprove List.append_nil by
  intro l
  simp

-- Test failed reprove - wrong tactic
/--
warning: declaration uses `sorry`
-/
#guard_msgs in
reprove simpleTheorem by
  sorry

-- Test failed reprove - incomplete proof
/-- error: (kernel) declaration has metavariables 'reprove_example✝' -/
#guard_msgs in
reprove withTactics by
  intro n

-- Test unknown declaration
/--
error: Unknown constant `nonExistentTheorem`
-/
#guard_msgs in
reprove nonExistentTheorem by
  simp

-- Test with a non-propositional type (creates example that succeeds)
def natValue : Nat := 42

reprove natValue by
  exact 42

-- Test with wrong proof
/--
error: Type mismatch
  "hello"
has type
  String
but is expected to have type
  Nat
-/
#guard_msgs in
reprove natValue by
  exact "hello"

-- Test complex type with implicit arguments
theorem hasImplicits {α : Type} (xs : List α) : xs.length ≥ 0 := by simp

reprove hasImplicits by simp

-- Test multiple declarations in one command
theorem theorem1 : 2 + 2 = 4 := by simp
theorem theorem2 : 3 + 3 = 6 := by simp
theorem theorem3 : 4 + 4 = 8 := by simp

reprove theorem1 theorem2 theorem3 by simp

-- Test namespace functionality
namespace Test

theorem namespaceTheorem : 5 + 5 = 10 := by simp

end Test

open Test

reprove namespaceTheorem by simp

-- Test multiple declarations where one fails due to unknown name
/--
error: Unknown constant `unknownTheorem`
-/
#guard_msgs in
reprove
  theorem1
  unknownTheorem
  theorem2
by simp

-- Test multiple declarations where tactic fails for one
theorem needsIntro : ∀ n : Nat, n = n := fun _ => rfl
theorem simpleEq : 1 = 1 := rfl

/--
error: Tactic `rfl` failed: Expected the goal to be a binary relation

Hint: Reflexivity tactics can only be used on goals of the form `x ~ x` or `R x x`

⊢ ∀ (n : Nat), n = n
-/
#guard_msgs in
reprove simpleEq needsIntro simpleTheorem by rfl

reprove Array.attach_empty by grind
