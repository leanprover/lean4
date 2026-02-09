/-!
This test contains functions with fixed parameter that appear in different orders.
-/

private axiom test_sorry : ∀ {α}, α

mutual
def foo (a : Nat) (n : Nat) (d : Nat) (m : Int) : Nat := bar d m (a + n + d + m.natAbs) n
decreasing_by exact test_sorry
def bar (b : Nat) (n : Int) (c : Nat) (m : Nat) : Nat := foo c m (b + n.natAbs + c + m) n
decreasing_by exact test_sorry
end

/--
info: equations:
theorem bar.eq_1 : ∀ (b : Nat) (n : Int) (c m : Nat), bar b n c m = foo c m (b + n.natAbs + c + m) n
-/
#guard_msgs in
#print equations bar

/--
info: foo.induct (n : Nat) (m : Int) (motive1 motive2 : Nat → Nat → Prop)
  (case1 : ∀ (a d : Nat), motive2 d (a + n + d + m.natAbs) → motive1 a d)
  (case2 : ∀ (b c : Nat), motive1 c (b + m.natAbs + c + n) → motive2 b c) (a d : Nat) : motive1 a d
-/
#guard_msgs in
#check foo.induct
/--
info: bar.induct (n : Nat) (m : Int) (motive1 motive2 : Nat → Nat → Prop)
  (case1 : ∀ (a d : Nat), motive2 d (a + n + d + m.natAbs) → motive1 a d)
  (case2 : ∀ (b c : Nat), motive1 c (b + m.natAbs + c + n) → motive2 b c) (b c : Nat) : motive2 b c
-/
#guard_msgs in
#check bar.induct
