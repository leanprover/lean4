/-!
This test contains functions with fixed parameter that have dependencies on varying parameter,
but only in annotations (optional parameters).
-/

private axiom test_sorry : ∀ {α}, α

namespace Ex1

mutual
def foo (varying : Nat) (fixed := varying) : Nat := bar fixed (varying + fixed)
decreasing_by exact test_sorry
def bar  (fixed : Nat) (varying : Nat) : Nat := foo (varying + fixed) fixed
decreasing_by exact test_sorry
end

/--
info: equations:
theorem Ex1.foo.eq_1 : ∀ (varying fixed : Nat), foo varying fixed = bar fixed (varying + fixed)
-/
#guard_msgs in
#print equations foo

/--
info: equations:
theorem Ex1.bar.eq_1 : ∀ (fixed varying : Nat), bar fixed varying = foo (varying + fixed) fixed
-/
#guard_msgs in
#print equations bar


/--
info: Ex1.foo.induct (fixed : Nat) (motive1 motive2 : Nat → Prop)
  (case1 : ∀ (varying : Nat), motive2 (varying + fixed) → motive1 varying)
  (case2 : ∀ (varying : Nat), motive1 (varying + fixed) → motive2 varying) (varying : Nat) : motive1 varying
-/
#guard_msgs in
#check foo.induct


end Ex1

namespace Ex2

mutual
def bar  (fixed : Nat) (varying : Nat) : Nat := foo (varying + fixed) fixed
decreasing_by exact test_sorry
def foo (varying : Nat) (fixed := varying) : Nat := bar fixed (varying + fixed)
decreasing_by exact test_sorry
end

/--
info: equations:
theorem Ex2.foo.eq_1 : ∀ (varying fixed : Nat), foo varying fixed = bar fixed (varying + fixed)
-/
#guard_msgs in
#print equations foo

/--
info: equations:
theorem Ex2.bar.eq_1 : ∀ (fixed varying : Nat), bar fixed varying = foo (varying + fixed) fixed
-/
#guard_msgs in
#print equations bar

/--
info: Ex2.foo.induct (fixed : Nat) (motive1 motive2 : Nat → Prop)
  (case1 : ∀ (varying : Nat), motive2 (varying + fixed) → motive1 varying)
  (case2 : ∀ (varying : Nat), motive1 (varying + fixed) → motive2 varying) (varying : Nat) : motive2 varying
-/
#guard_msgs in
#check foo.induct


end Ex2
