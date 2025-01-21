set_option grind.debug true

/--
info: [grind.offset.internalize.term] a1 ↦ #0
[grind.offset.internalize.term] a2 ↦ #1
[grind.offset.internalize] a1 + 1 ≤ a2 ↦ #0 + 1 ≤ #1
[grind.offset.internalize.term] a3 ↦ #2
[grind.offset.internalize] a2 ≤ a3 + 2 ↦ #1 ≤ #2 + 2
[grind.offset.internalize.term] a4 ↦ #3
[grind.offset.internalize] a3 ≤ a4 ↦ #2 ≤ #3
-/
#guard_msgs (info) in
set_option trace.grind.offset.internalize true in
example (a1 a2 a3) :
        a1 + 1 ≤ a2 → a2 ≤ a3 + 2 → a3 ≤ a4 → False := by
  fail_if_success grind
  sorry

/--
info: [grind.offset.internalize.term] a1 ↦ #0
[grind.offset.internalize.term] a2 ↦ #1
[grind.offset.dist] #0 + 1 ≤ #1
[grind.offset.internalize.term] a3 ↦ #2
[grind.offset.dist] #1 ≤ #2
[grind.offset.dist] #0 + 1 ≤ #2
-/
#guard_msgs (info) in
set_option trace.grind.offset.internalize.term true in
set_option trace.grind.offset.dist true in
example (a1 a2 a3 : Nat) :
        a1 + 1 ≤ a2 → a2 ≤ a3 → False := by
  fail_if_success grind
  sorry


/--
info: [grind.offset.internalize.term] a1 ↦ #0
[grind.offset.internalize.term] a2 ↦ #1
[grind.offset.dist] #0 + 1 ≤ #1
[grind.offset.internalize.term] a3 ↦ #2
[grind.offset.dist] #1 + 2 ≤ #2
[grind.offset.dist] #0 + 3 ≤ #2
-/
#guard_msgs (info) in
set_option trace.grind.offset.internalize.term true in
set_option trace.grind.offset.dist true in
example (a1 a2 a3 : Nat) :
        a1 + 1 ≤ a2 → a2 + 2 ≤ a3 → False := by
  fail_if_success grind
  sorry

/--
info: [grind.offset.internalize.term] a1 ↦ #0
[grind.offset.internalize.term] a2 ↦ #1
[grind.offset.dist] #0 + 1 ≤ #1
[grind.offset.internalize.term] a3 ↦ #2
[grind.offset.dist] #1 ≤ #2 + 2
[grind.offset.dist] #0 ≤ #2 + 1
-/
#guard_msgs (info) in
set_option trace.grind.offset.internalize.term true in
set_option trace.grind.offset.dist true in
example (a1 a2 a3 : Nat) :
        a1 + 1 ≤ a2 → a2 ≤ a3 + 2 → False := by
  fail_if_success grind
  sorry

/--
info: [grind.offset.internalize.term] a1 ↦ #0
[grind.offset.internalize.term] a2 ↦ #1
[grind.offset.dist] #0 ≤ #1
[grind.offset.internalize.term] a3 ↦ #2
[grind.offset.dist] #1 ≤ #2
[grind.offset.dist] #0 ≤ #2
-/
#guard_msgs (info) in
set_option trace.grind.offset.internalize.term true in
set_option trace.grind.offset.dist true in
example (a1 a2 a3 : Nat) :
        a1 ≤ a2 → a2 ≤ a3 → False := by
  fail_if_success grind
  sorry

/--
info: [grind.offset.internalize.term] a1 ↦ #0
[grind.offset.internalize.term] a2 ↦ #1
[grind.offset.dist] #0 ≤ #1
[grind.offset.internalize.term] a3 ↦ #2
[grind.offset.dist] #1 + 2 ≤ #2
[grind.offset.dist] #0 + 2 ≤ #2
-/
#guard_msgs (info) in
set_option trace.grind.offset.internalize.term true in
set_option trace.grind.offset.dist true in
example (a1 a2 a3 : Nat) :
        a1 ≤ a2 → a2 + 2 ≤ a3 → False := by
  fail_if_success grind
  sorry

/--
info: [grind.offset.internalize.term] a1 ↦ #0
[grind.offset.internalize.term] a2 ↦ #1
[grind.offset.dist] #0 ≤ #1
[grind.offset.internalize.term] a3 ↦ #2
[grind.offset.dist] #1 ≤ #2 + 5
[grind.offset.dist] #0 ≤ #2 + 5
-/
#guard_msgs (info) in
set_option trace.grind.offset.internalize.term true in
set_option trace.grind.offset.dist true in
example (a1 a2 a3 : Nat) :
        a1 ≤ a2 → a2 ≤ a3 + 5 → False := by
  fail_if_success grind
  sorry

/--
info: [grind.offset.internalize.term] a1 ↦ #0
[grind.offset.internalize.term] a2 ↦ #1
[grind.offset.dist] #0 ≤ #1 + 5
[grind.offset.internalize.term] a3 ↦ #2
[grind.offset.dist] #1 ≤ #2
[grind.offset.dist] #0 ≤ #2 + 5
-/
#guard_msgs (info) in
set_option trace.grind.offset.internalize.term true in
set_option trace.grind.offset.dist true in
example (a1 a2 a3 : Nat) :
        a1 ≤ a2 + 5 → a2 ≤ a3 → False := by
  fail_if_success grind
  sorry

/--
info: [grind.offset.internalize.term] a1 ↦ #0
[grind.offset.internalize.term] a2 ↦ #1
[grind.offset.dist] #0 ≤ #1 + 5
[grind.offset.internalize.term] a3 ↦ #2
[grind.offset.dist] #1 + 2 ≤ #2
[grind.offset.dist] #0 ≤ #2 + 3
-/
#guard_msgs (info) in
set_option trace.grind.offset.internalize.term true in
set_option trace.grind.offset.dist true in
example (a1 a2 a3 : Nat) :
        a1 ≤ a2 + 5 → a2 + 2 ≤ a3 → False := by
  fail_if_success grind
  sorry

/--
info: [grind.offset.internalize.term] a1 ↦ #0
[grind.offset.internalize.term] a2 ↦ #1
[grind.offset.dist] #0 ≤ #1 + 5
[grind.offset.internalize.term] a3 ↦ #2
[grind.offset.dist] #1 ≤ #2 + 2
[grind.offset.dist] #0 ≤ #2 + 7
-/
#guard_msgs (info) in
set_option trace.grind.offset.internalize.term true in
set_option trace.grind.offset.dist true in
example (a1 a2 a3 : Nat) :
        a1 ≤ a2 + 5 → a2 ≤ a3 + 2 → False := by
  fail_if_success grind
  sorry


set_option trace.grind.debug.offset.proof true in
example (a1 a2 a3 : Nat) :
        a1 ≤ a2 + 5 → a2 ≤ a3 + 2 → False := by
  fail_if_success grind
  sorry

/--
info: [grind.offset.internalize.term] a1 ↦ #0
[grind.offset.internalize.term] a2 ↦ #1
[grind.offset.dist] #0 ≤ #1 + 2
[grind.offset.internalize.term] a3 ↦ #2
[grind.offset.dist] #1 + 3 ≤ #2
[grind.offset.dist] #0 + 1 ≤ #2
-/
#guard_msgs (info) in
set_option trace.grind.offset.internalize.term true in
set_option trace.grind.offset.dist true in
example (a1 a2 a3 : Nat) : a1 ≤ a2 + 2 → a2 + 3 ≤ a3 → False := by
  fail_if_success grind
  sorry

/--
info: [grind.offset.internalize.term] a2 ↦ #0
[grind.offset.internalize.term] a1 ↦ #1
[grind.offset.dist] #1 + 3 ≤ #0
[grind.offset.internalize.term] a3 ↦ #2
[grind.offset.dist] #0 + 3 ≤ #2
[grind.offset.dist] #1 + 6 ≤ #2
-/
#guard_msgs (info) in
set_option trace.grind.offset.internalize.term true in
set_option trace.grind.offset.dist true in
example (p : Prop) (a1 a2 a3 : Nat) : (p ↔ a2 ≤ a1 + 2) → ¬p → a2 + 3 ≤ a3 → False := by
  fail_if_success grind
  sorry

/--
info: [grind.offset.internalize.term] a2 ↦ #0
[grind.offset.internalize.term] a1 ↦ #1
[grind.offset.dist] #1 ≤ #0 + 1
[grind.offset.internalize.term] a3 ↦ #2
[grind.offset.dist] #0 + 3 ≤ #2
[grind.offset.dist] #1 + 2 ≤ #2
-/
#guard_msgs (info) in
set_option trace.grind.offset.internalize.term true in
set_option trace.grind.offset.dist true in
example (p : Prop) (a1 a2 a3 : Nat) : (p ↔ a2 + 2 ≤ a1) → ¬p → a2 + 3 ≤ a3 → False := by
  fail_if_success grind
  sorry

/--
info: [grind.offset.internalize.term] a2 ↦ #0
[grind.offset.internalize.term] a1 ↦ #1
[grind.offset.dist] #1 + 1 ≤ #0
[grind.offset.internalize.term] a3 ↦ #2
[grind.offset.dist] #0 + 3 ≤ #2
[grind.offset.dist] #1 + 4 ≤ #2
-/
#guard_msgs (info) in
set_option trace.grind.offset.internalize.term true in
set_option trace.grind.offset.dist true in
example (p : Prop) (a1 a2 a3 : Nat) : (p ↔ a2 ≤ a1) → ¬p → a2 + 3 ≤ a3 → False := by
  fail_if_success grind
  sorry

/--
info: [grind.offset.internalize.term] a2 ↦ #0
[grind.offset.internalize.term] a1 ↦ #1
[grind.offset.dist] #1 ≤ #0
[grind.offset.internalize.term] a3 ↦ #2
[grind.offset.dist] #0 + 3 ≤ #2
[grind.offset.dist] #1 + 3 ≤ #2
-/
#guard_msgs (info) in
set_option trace.grind.offset.internalize.term true in
set_option trace.grind.offset.dist true in
example (p : Prop) (a1 a2 a3 : Nat) : (p ↔ a2 + 1 ≤ a1) → ¬p → a2 + 3 ≤ a3 → False := by
  fail_if_success grind
  sorry

example (a b c : Nat) : a ≤ b → b + 2 ≤ c → a + 1 ≤ c := by
  grind
example (a b c : Nat) : a ≤ b → b ≤ c → a ≤ c := by
  grind
example (a b c : Nat) : a + 1 ≤ b → b + 1 ≤ c → a + 2 ≤ c := by
  grind
example (a b c : Nat) : a + 1 ≤ b → b + 1 ≤ c → a + 1 ≤ c := by
  grind
example (a b c : Nat) : a + 1 ≤ b → b ≤ c + 2 → a ≤ c + 1 := by
  grind
example (a b c : Nat) : a + 2 ≤ b → b ≤ c + 2 → a ≤ c := by
  grind

theorem ex1 (p : Prop) (a1 a2 a3 : Nat) : (p ↔ a2 ≤ a1) → ¬p → a2 + 3 ≤ a3 → (p ↔ a4 ≤ a3 + 2) → a1 ≤ a4 := by
  grind

/--
info: theorem ex1 : ∀ {a4 : Nat} (p : Prop) (a1 a2 a3 : Nat),
  (p ↔ a2 ≤ a1) → ¬p → a2 + 3 ≤ a3 → (p ↔ a4 ≤ a3 + 2) → a1 ≤ a4 :=
fun {a4} p a1 a2 a3 =>
  intro_with_eq (p ↔ a2 ≤ a1) (p = (a2 ≤ a1)) (¬p → a2 + 3 ≤ a3 → (p ↔ a4 ≤ a3 + 2) → a1 ≤ a4) (iff_eq p (a2 ≤ a1))
    fun a a_1 a_2 =>
    intro_with_eq (p ↔ a4 ≤ a3 + 2) (p = (a4 ≤ a3 + 2)) (a1 ≤ a4) (iff_eq p (a4 ≤ a3 + 2)) fun a_3 =>
      Classical.byContradiction
        (intro_with_eq (¬a1 ≤ a4) (a4 + 1 ≤ a1) False (Nat.not_le_eq a1 a4) fun x =>
          Nat.unsat_lo_lo a4 a1 1 7 rfl_true x
            (Nat.lo_lo a1 a2 a4 1 6 (Nat.of_le_eq_false a2 a1 (Eq.trans (Eq.symm a) (eq_false a_1)))
              (Nat.lo_lo a2 a3 a4 3 3 a_2 (Nat.of_ro_eq_false a4 a3 2 (Eq.trans (Eq.symm a_3) (eq_false a_1))))))
-/
#guard_msgs (info) in
open Lean Grind in
#print ex1

/-! Propagate `cnstr = False` tests -/

-- The following example is solved by `grind` using constraint propagation and 0 case-splits.
#guard_msgs (info) in
set_option trace.grind.split true in
example (p q r s : Prop) (a b : Nat) : a ≤ b → b + 2 ≤ c → (a + 1 ≤ c ↔ p) → (a + 2 ≤ c ↔ s) → (a ≤ c ↔ q) → (a ≤ c + 4 ↔ r) → p ∧ q ∧ r ∧ s := by
  grind (splits := 0)

-- The following example is solved by `grind` using constraint propagation and 0 case-splits.
#guard_msgs (info) in
set_option trace.grind.split true in
example (p q : Prop) (a b : Nat) : a ≤ b → b ≤ c → (a ≤ c ↔ p) → (a ≤ c + 1 ↔ q) → p ∧ q := by
  grind (splits := 0)

-- The following example is solved by `grind` using constraint propagation and 0 case-splits.
#guard_msgs (info) in
set_option trace.grind.split true in
example (p q : Prop) (a b : Nat) : a ≤ b → b ≤ c + 1 → (a ≤ c + 1 ↔ p) → (a ≤ c + 2 ↔ q) → p ∧ q := by
  grind (splits := 0)


-- The following example is solved by `grind` using constraint propagation and 0 case-splits.
#guard_msgs (info) in
set_option trace.grind.split true in
example (p r s : Prop) (a b : Nat) : a ≤ b → b + 2 ≤ c → (c ≤ a ↔ p) → (c ≤ a + 1 ↔ s) → (c + 1 ≤ a ↔ r) → ¬p ∧ ¬r ∧ ¬s := by
  grind (splits := 0)

-- The following example is solved by `grind` using constraint propagation and 0 case-splits.
#guard_msgs (info) in
set_option trace.grind.split true in
example (p r : Prop) (a b : Nat) : a ≤ b → b ≤ c → (c + 1 ≤ a ↔ p) → (c + 2 ≤ a + 1 ↔ r) → ¬p ∧ ¬r := by
  grind (splits := 0)

-- The following example is solved by `grind` using constraint propagation and 0 case-splits.
#guard_msgs (info) in
set_option trace.grind.split true in
example (p r : Prop) (a b : Nat) : a  ≤ b → b ≤ c + 3 → (c + 5 ≤ a ↔ p) → (c + 4 ≤ a ↔ r) → ¬p ∧ ¬r := by
  grind (splits := 0)

/-! Propagate `cnstr = False` tests, but with different internalization order -/

-- The following example is solved by `grind` using constraint propagation and 0 case-splits.
#guard_msgs (info) in
set_option trace.grind.split true in
example (p q r s : Prop) (a b : Nat) : (a + 1 ≤ c ↔ p) → (a + 2 ≤ c ↔ s) → (a ≤ c ↔ q) → (a ≤ c + 4 ↔ r) → a ≤ b → b + 2 ≤ c → p ∧ q ∧ r ∧ s := by
  grind (splits := 0)

-- The following example is solved by `grind` using constraint propagation and 0 case-splits.
#guard_msgs (info) in
set_option trace.grind.split true in
example (p q : Prop) (a b : Nat) : (a ≤ c ↔ p) → (a ≤ c + 1 ↔ q) → a ≤ b → b ≤ c → p ∧ q := by
  grind (splits := 0)

-- The following example is solved by `grind` using constraint propagation and 0 case-splits.
#guard_msgs (info) in
set_option trace.grind.split true in
example (p q : Prop) (a b : Nat) : (a ≤ c + 1 ↔ p) → (a ≤ c + 2 ↔ q) → a ≤ b → b ≤ c + 1 → p ∧ q := by
  grind (splits := 0)

-- The following example is solved by `grind` using constraint propagation and 0 case-splits.
#guard_msgs (info) in
set_option trace.grind.split true in
example (p r s : Prop) (a b : Nat) : (c ≤ a ↔ p) → (c ≤ a + 1 ↔ s) → (c + 1 ≤ a ↔ r) → a ≤ b → b + 2 ≤ c → ¬p ∧ ¬r ∧ ¬s := by
  grind (splits := 0)

-- The following example is solved by `grind` using constraint propagation and 0 case-splits.
#guard_msgs (info) in
set_option trace.grind.split true in
example (p r : Prop) (a b : Nat) : (c + 1 ≤ a ↔ p) → (c + 2 ≤ a + 1 ↔ r) → a ≤ b → b ≤ c → ¬p ∧ ¬r := by
  grind (splits := 0)

-- The following example is solved by `grind` using constraint propagation and 0 case-splits.
#guard_msgs (info) in
set_option trace.grind.split true in
example (p r : Prop) (a b : Nat) : (c + 5 ≤ a ↔ p) → (c + 4 ≤ a ↔ r) → a ≤ b → b ≤ c + 3 → ¬p ∧ ¬r := by
  grind (splits := 0)
