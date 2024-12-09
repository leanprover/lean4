axiom a : Nat
axiom b : Nat
axiom a_eq_b : a = b

axiom P : Nat → Nat → Prop

-- Warm-up: rewriting in the forward direction

/-- error: simp made no progress -/
#guard_msgs in example : P a b := by simp

attribute [simp] a_eq_b

/--
error: unsolved goals
⊢ P b b
-/
#guard_msgs in example : P a b := by simp

attribute [-simp] a_eq_b

/-- error: simp made no progress -/
#guard_msgs in example : P a b := by simp

-- Re-adding an attribute after [-simp] does not work, see
-- https://github.com/leanprover/lean4/issues/5868

attribute [simp] a_eq_b

/-- error: simp made no progress -/
#guard_msgs in example : P a b := by simp

-- so this test use new copies of `a_eq_b` for now

axiom a_eq_b_2 : a = b

attribute [simp ←] a_eq_b_2

/--
error: unsolved goals
⊢ P a a
-/
#guard_msgs in example : P a b := by simp

-- Removing the attribute works, no matter the direction

attribute [-simp] a_eq_b_2

/-- error: simp made no progress -/
#guard_msgs in example : P a b := by simp

-- Setting one should erase the other

axiom a_eq_b_3 : a = b

attribute [simp ←] a_eq_b_3
attribute [simp] a_eq_b_3

/--
error: unsolved goals
⊢ P b b
-/
#guard_msgs in example : P a b := by simp


-- The erasure is sticky:
attribute [simp ←] a_eq_b_3
/-- error: simp made no progress -/
#guard_msgs in example : P a b := by simp

axiom a_eq_b_4 : a = b

attribute [simp] a_eq_b_4
attribute [simp ←] a_eq_b_4

/--
error: unsolved goals
⊢ P a a
-/
#guard_msgs in example : P a b := by simp


-- Some more error conditions

axiom P_a : P a a

/-- error: invalid '←' modifier in rewrite rule to 'True' -/
#guard_msgs in
attribute [simp ←] P_a

/-- error: invalid 'simp', it is not a proposition nor a definition (to unfold) -/
#guard_msgs in
attribute [simp ←] P

/-- error: invalid '←' modifier, 'id' is a declaration name to be unfolded -/
#guard_msgs in
attribute [simp ←] id
