
namespace Test
/--
error: incomplete set of termination hints:
This function is mutually recursive with Test.f, Test.h, and Test.i, which do not have a termination hint.
The present clause is ignored.
-/
#guard_msgs in
mutual
  def f : Nat → α → α → α
    | 0, a, b => a
    | n+1, a, b => g n a b |>.1

  def g : Nat → α → α → (α × α)
    | 0, a, b => (a, b)
    | n+1, a, b => (h n a b, a)
  termination_by n _ _ => n -- Error

  def h : Nat → α → α → α
    | 0, a, b => b
    | n+1, a, b => i n a b

  def i : Nat → α → α → α
    | 0, a, b => b
    | n+1, a, b => f n a b
end
end Test

namespace Test2
/--
error: Incompatible termination hint; this function is mutually recursive with Test2.f, which is marked as `termination_by structural` so this one also needs to be marked `structural`.
-/
#guard_msgs in
mutual
  def f : Nat → α → α → α
    | 0, a, b => a
    | n+1, a, b => g n a b |>.1
  termination_by structural n _ _ => n

  def g : Nat → α → α → (α × α)
    | 0, a, b => (a, b)
    | n+1, a, b => (h n a b, a)
  termination_by n _ _ => n -- Error

  def h : Nat → α → α → α
    | 0, a, b => b
    | n+1, a, b => f n a b
  termination_by n _ _ => n
end
end Test2

namespace Test3
/--
error: Incompatible termination hint; this function is mutually recursive with Test3.f, which is not marked as `structural` so this one cannot be `structural` either.
-/
#guard_msgs in
mutual
  def f : Nat → α → α → α
    | 0, a, b => a
    | n+1, a, b => g n a b |>.1
  termination_by n _ _ => n

  def g : Nat → α → α → (α × α)
    | 0, a, b => (a, b)
    | n+1, a, b => (h n a b, a)
  termination_by structural n _ _ => n -- Error

  def h : Nat → α → α → α
    | 0, a, b => b
    | n+1, a, b => f n a b
  termination_by structural n _ _ => n
end
end Test3

namespace Test4

/--
error: Incompatible termination hint; this function is mutually recursive with Test4.f, which is not marked as `structural` so this one cannot be `structural` either.
-/
#guard_msgs in
mutual
  def f : Nat → α → α → α
    | 0, a, b => a
    | n+1, a, b => g n a b |>.1
  termination_by n _ _ => n

  def g : Nat → α → α → (α × α)
    | 0, a, b => (a, b)
    | n+1, a, b => (h n a b, a)
  termination_by n _ _ => n

  def h : Nat → α → α → α
    | 0, a, b => b
    | n+1, a, b => f n a b
  termination_by structural n _ _ => n -- Error
end
end Test4

namespace Test5
/--
error: Incompatible termination hint; this function is marked as structurally recursive, so no explicit termination proof is needed.
-/
#guard_msgs in
mutual
  def f : Nat → α → α → α
    | 0, a, b => a
    | n+1, a, b => g n a b |>.1
  termination_by structural n _ _ => n

  def g : Nat → α → α → (α × α)
    | 0, a, b => (a, b)
    | n+1, a, b => (h n a b, a)
  termination_by structural n _ _ => n
  decreasing_by sorry -- Error

  def h : Nat → α → α → α
    | 0, a, b => b
    | n+1, a, b => f n a b
  termination_by structural n _ _ => n
end
end Test5

namespace Test6
/--
error: Incompatible termination hint; this function is mutually recursive with Test6.f, which is marked as `partial_fixpoint` so this one also needs to be marked `partial_fixpoint`.
-/
#guard_msgs in
mutual
  def f (x : Nat) : Prop :=
    g  (x + 1)
  partial_fixpoint

  def g (x : Nat) : Prop := f (x + 1)
  inductive_fixpoint
end
end Test6


namespace Test7
/--
error: Incompatible termination hint; this function is mutually recursive with Test7.f, which is marked as `coinductive_fixpoint` so this one also needs to be marked `inductive_fixpoint` or `coinductive_fixpoint`.
-/
#guard_msgs in
mutual
  def f (x : Nat) : Prop :=
    g (x + 1)
  coinductive_fixpoint

  def g (x : Nat) : Prop :=
    f (x + 1)
  partial_fixpoint
end
end Test7

namespace Test8
/--
error: Incompatible termination hint; this function is mutually recursive with Test8.f, which is not also marked as `partial_fixpoint`, so this one cannot be either.
-/
#guard_msgs in
mutual
  def f (x : Nat) : Prop :=
    g (x + 1)
    termination_by?

  def g (x : Nat) : Prop :=
    f (x + 1)
    partial_fixpoint
end
end Test8

namespace Test9
/--
error: Incompatible termination hint; this function is mutually recursive with Test9.f, which is not also marked as `inductive_fixpoint` or `coinductive_fixpoint`, so this one cannot be either.
-/
#guard_msgs in
mutual
  def f (x : Nat) : Prop :=
    g (x + 1)
    termination_by?

  def g (x : Nat) : Prop :=
    f (x + 1)
    inductive_fixpoint
end
end Test9

namespace Test10
/--
error: Incompatible termination hint; this function is mutually recursive with Test10.f, which is marked as `coinductive_fixpoint` so this one also needs to be marked `inductive_fixpoint` or `coinductive_fixpoint`.
-/
#guard_msgs in
mutual
  def f (x : Nat) : Prop :=
    g (x + 1)
    coinductive_fixpoint

  def g (x : Nat) : Prop :=
    f (x + 1)
    termination_by?
end
end Test10

namespace Test11
/--
error: Incompatible termination hint; this function is mutually recursive with Test11.f, which is marked as `partial_fixpoint` so this one also needs to be marked `partial_fixpoint`.
-/
#guard_msgs in
mutual
  def f (x : Nat) : Prop :=
    g (x +1)
    partial_fixpoint

  def g (x : Nat) : Prop :=
    f (x + 1)
end
end Test11
