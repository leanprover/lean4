axiom testSorry : α

opaque a : Nat
opaque b : Nat

theorem ab : a = b := testSorry
theorem ba : b = a := testSorry
theorem aa : a = id a := testSorry

/--
warning: Ignoring looping simp theorem: aa
---
error: unsolved goals
⊢ a = 23
-/
#guard_msgs in
example : id a = 23 := by simp +loopProtection -failIfUnchanged [aa]

/--
warning: Ignoring jointly looping simp theorems: ab and ba
---
error: unsolved goals
⊢ a = 23
-/
#guard_msgs in
example : a = 23 := by simp +loopProtection -failIfUnchanged [ab, ba]

/--
warning: Ignoring jointly looping simp theorems: ← ba and ← ab
---
error: unsolved goals
⊢ a = 23
-/
#guard_msgs in
example : a = 23 := by simp +loopProtection -failIfUnchanged [← ab, ← ba]

-- Local theorems are ignored:
/--
error: unsolved goals
h : b = 23
⊢ b = 23
-/
#guard_msgs in
example (h : b = 23) : a = 23 := by simp +loopProtection -failIfUnchanged [ab, h]

/-! Check that we cache the protection result (both positive and negative) -/

opaque id' : Nat → Nat
theorem id'_eq (n : Nat) : id' n = n := testSorry
theorem id'_eq_bad (n : Nat) : id' n = id' (id' n) := testSorry

/--
trace: [Meta.Tactic.simp.loopProtection] ✅️ loop-checking id'_eq:1000
[Meta.Tactic.simp.loopProtection] ✅️ loop-checking eq_self:1000
-/
#guard_msgs in
set_option trace.Meta.Tactic.simp.loopProtection true in
example : id' 1 + id' 2 = id' 3 := by simp +loopProtection -failIfUnchanged [id'_eq]

/--
warning: Ignoring looping simp theorem: id'_eq_bad
---
error: unsolved goals
⊢ id' 1 + id' 2 = id' 3
---
trace: [Meta.Tactic.simp.loopProtection] ❌️ loop-checking id'_eq_bad:1000
-/
#guard_msgs in
set_option trace.Meta.Tactic.simp.loopProtection true in
example : id' 1 + id' 2 = id' 3 := by simp +loopProtection -failIfUnchanged [id'_eq_bad]


/-! Examples from the original RFC -/

variable (P : Nat → Prop)
/--
warning: Ignoring jointly looping simp theorems: Nat.add_assoc and (Nat.add_assoc _ _ _).symm
---
error: simp made no progress
-/
#guard_msgs in
example (a b c : Nat) : P (a + b + c) := by simp +loopProtection [Nat.add_assoc, (Nat.add_assoc _ _ _).symm]

inductive Tree (α : Type) where | node : α → List (Tree α) → Tree α
def Tree.children : Tree α → List (Tree α) | .node _ ts => ts
def Tree.size (t : Tree α) := 1 + List.sum (t.children.attach.map (fun ⟨c,_⟩  => c.size))
decreasing_by simp_wf; cases t; simp_all [Tree.children]; decreasing_trivial

/--
warning: Ignoring looping simp theorem: Tree.size.eq_1
---
error: simp made no progress
-/
#guard_msgs in
example (t : Tree α) : 0 < t.size := by simp +loopProtection [Tree.size]


/--
TODO: Identifiyng looping theorems by their origin is not enough,
as the elements of conjunctions would clash.
-/

theorem b1ab : b = 1 ∧ a = b := testSorry

/--
warning: Ignoring looping simp theorem: b1ab
---
error: simp made no progress
-/
#guard_msgs in
example
  (h2 : a > 0) : True := by
  simp +loopProtection only [b1ab] at h2

-- Same, with local theorems (should we ever support them):

/-- error: simp made no progress -/
#guard_msgs in
example
  (a b : Nat)
  (h1 : b = 1 ∧ a = b )
  (h2 : a > 0) : True := by
  simp +loopProtection only [h1] at h2
