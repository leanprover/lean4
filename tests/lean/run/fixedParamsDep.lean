/-!
This test contains functions with fixed parameter that have dependencies on varying parameter,
which can happen when those dependencies reduce away.
-/

def const (x : α) (_ : β) : α := x

private axiom test_sorry : ∀ {α}, α

namespace Ex1

mutual
def foo (varying : Nat) (fixed : const Nat varying) : Nat := bar fixed (Nat.add varying fixed)
decreasing_by exact test_sorry
def bar  (fixed : Nat) (varying : Nat) : Nat := foo (varying + fixed) fixed
decreasing_by exact test_sorry
end

/--
info: equations:
theorem Ex1.foo.eq_1 : ∀ (varying : Nat) (fixed : const Nat varying), foo varying fixed = bar fixed (varying.add fixed)
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
info: Ex1.foo.induct (motive1 : (varying : Nat) → const Nat varying → Prop) (motive2 : Nat → Nat → Prop)
  (case1 : ∀ (varying : Nat) (fixed : const Nat varying), motive2 fixed (varying.add fixed) → motive1 varying fixed)
  (case2 : ∀ (fixed varying : Nat), motive1 (varying + fixed) fixed → motive2 fixed varying) (varying : Nat)
  (fixed : const Nat varying) : motive1 varying fixed
-/
#guard_msgs in
#check foo.induct


end Ex1

namespace Ex2

mutual
def bar  (fixed : Nat) (varying : Nat) : Nat := foo (varying + fixed) fixed
decreasing_by exact test_sorry
def foo (varying : Nat) (fixed : const Nat varying) : Nat := bar fixed (Nat.add varying fixed)
decreasing_by exact test_sorry
end

/--
info: equations:
theorem Ex2.foo.eq_1 : ∀ (varying : Nat) (fixed : const Nat varying), foo varying fixed = bar fixed (varying.add fixed)
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
info: Ex2.foo.induct (motive1 : Nat → Nat → Prop) (motive2 : (varying : Nat) → const Nat varying → Prop)
  (case1 : ∀ (fixed varying : Nat), motive2 (varying + fixed) fixed → motive1 fixed varying)
  (case2 : ∀ (varying : Nat) (fixed : const Nat varying), motive1 fixed (varying.add fixed) → motive2 varying fixed)
  (varying : Nat) (fixed : const Nat varying) : motive2 varying fixed
-/
#guard_msgs in
#check foo.induct


end Ex2
