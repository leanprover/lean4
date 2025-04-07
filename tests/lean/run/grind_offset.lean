opaque g : Nat → Nat

@[simp] def f (a : Nat) :=
  match a with
  | 0 => 10
  | x+1 => g (f x)

set_option trace.grind.ematch.pattern true
set_option trace.grind.ematch.instance true
set_option trace.grind.assert true

/-- info: [grind.ematch.pattern] f.eq_2: [f (#0 + 1)] -/
#guard_msgs in
grind_pattern f.eq_2 => f (x + 1)


/--
info: [grind.assert] f (y + 1) = a
[grind.assert] ¬a = g (f y)
[grind.ematch.instance] f.eq_2: f y.succ = g (f y)
[grind.assert] f (y + 1) = g (f y)
-/
#guard_msgs (info) in
example : f (y + 1) = a → a = g (f y) := by
  grind

/--
info: [grind.assert] f 1 = a
[grind.assert] ¬a = g (f 0)
[grind.ematch.instance] f.eq_2: f (Nat.succ 0) = g (f 0)
[grind.assert] f 1 = g (f 0)
-/
#guard_msgs (info) in
example : f 1 = a → a = g (f 0) := by
  grind

/--
info: [grind.assert] f 10 = a
[grind.assert] ¬a = g (f 9)
[grind.ematch.instance] f.eq_2: f (Nat.succ 8) = g (f 8)
[grind.ematch.instance] f.eq_2: f (Nat.succ 9) = g (f 9)
[grind.assert] f 9 = g (f 8)
[grind.assert] f 10 = g (f 9)
-/
#guard_msgs (info) in
example : f 10 = a → a = g (f 9) := by
  grind

/--
info: [grind.assert] f (c + 2) = a
[grind.assert] ¬a = g (g (f c))
[grind.ematch.instance] f.eq_2: f (c + 1).succ = g (f (c + 1))
[grind.assert] f (c + 2) = g (f (c + 1))
[grind.ematch.instance] f.eq_2: f c.succ = g (f c)
[grind.assert] f (c + 1) = g (f c)
-/
#guard_msgs (info) in
example : f (c + 2) = a → a = g (g (f c)) := by
  grind

@[simp] def foo (a : Nat) :=
  match a with
  | 0 => 10
  | 1 => 10
  | a+2 => g (foo a)

/-- info: [grind.ematch.pattern] foo.eq_3: [foo (#0 + 2)] -/
#guard_msgs in
grind_pattern foo.eq_3 => foo (a_2 + 2)

-- The instance is correctly found in the following example.
-- TODO: to complete the proof, we need linear arithmetic support to prove that `b + 2 = c + 1`.
/--
info: [grind.assert] foo (c + 1) = a
[grind.assert] c = b + 1
[grind.assert] ¬a = g (foo b)
[grind.ematch.instance] foo.eq_3: foo b.succ.succ = g (foo b)
[grind.assert] foo (b + 2) = g (foo b)
[grind.assert] -1 * ↑b ≤ 0
[grind.assert] -1 * ↑c ≤ 0
-/
#guard_msgs (info) in
example : foo (c + 1) = a → c = b + 1 → a = g (foo b) := by
  grind

set_option trace.grind.assert false

/--
info: [grind.ematch.instance] f.eq_2: f (x + 99).succ = g (f (x + 99))
[grind.ematch.instance] f.eq_2: f (x + 98).succ = g (f (x + 98))
-/
#guard_msgs (info) in
example : f (x + 100) = a → a = b := by
  fail_if_success grind (ematch := 2)
  sorry

/--
info: [grind.ematch.instance] f.eq_2: f (x + 99).succ = g (f (x + 99))
[grind.ematch.instance] f.eq_2: f (x + 98).succ = g (f (x + 98))
[grind.ematch.instance] f.eq_2: f (x + 97).succ = g (f (x + 97))
[grind.ematch.instance] f.eq_2: f (x + 96).succ = g (f (x + 96))
[grind.ematch.instance] f.eq_2: f (x + 95).succ = g (f (x + 95))
-/
#guard_msgs (info) in
example : f (x + 100) = a → a = b := by
  fail_if_success grind (ematch := 5)
  sorry

/--
info: [grind.ematch.instance] f.eq_2: f (x + 99).succ = g (f (x + 99))
[grind.ematch.instance] f.eq_2: f (x + 98).succ = g (f (x + 98))
[grind.ematch.instance] f.eq_2: f (x + 97).succ = g (f (x + 97))
[grind.ematch.instance] f.eq_2: f (x + 96).succ = g (f (x + 96))
-/
#guard_msgs (info) in
example : f (x + 100) = a → a = b := by
  fail_if_success grind (ematch := 100) (instances := 4)
  sorry

/--
info: [grind.ematch.instance] f.eq_2: f (y + 9).succ = g (f (y + 9))
[grind.ematch.instance] f.eq_2: f (x + 99).succ = g (f (x + 99))
[grind.ematch.instance] f.eq_2: f (x + 98).succ = g (f (x + 98))
[grind.ematch.instance] f.eq_2: f (y + 8).succ = g (f (y + 8))
[grind.ematch.instance] f.eq_2: f (y + 7).succ = g (f (y + 7))
-/
#guard_msgs (info) in
example : f (x + 100) = a → f (y + 10) = c → a = b := by
  fail_if_success grind (ematch := 100) (instances := 5)
  sorry

/--
info: [grind.ematch.instance] f.eq_2: f (x + 99).succ = g (f (x + 99))
[grind.ematch.instance] f.eq_2: f (x + 98).succ = g (f (x + 98))
-/
#guard_msgs (info) in
example : f (x + 100) = a → a = b := by
  fail_if_success grind (gen := 2)
  sorry

/--
info: [grind.ematch.instance] f.eq_2: f (x + 99).succ = g (f (x + 99))
[grind.ematch.instance] f.eq_2: f (x + 98).succ = g (f (x + 98))
[grind.ematch.instance] f.eq_2: f (x + 97).succ = g (f (x + 97))
[grind.ematch.instance] f.eq_2: f (x + 96).succ = g (f (x + 96))
[grind.ematch.instance] f.eq_2: f (x + 95).succ = g (f (x + 95))
-/
#guard_msgs (info) in
example : f (x + 100) = a → a = b := by
  fail_if_success grind (gen := 5)
  sorry
