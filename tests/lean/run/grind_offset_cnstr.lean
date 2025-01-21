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
