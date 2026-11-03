/-!
Cases where the equation lemmas still copy values that could stay shared. The `#guard_msgs`
blocks are the expected results; they fail on the current implementation.
-/

-- 1. A `have` inside the value of a `have` whose `match` is split.
def innerHave (x : Nat) : Nat :=
  have a :=
    have b := x * x + x
    match x with
    | 0 => b
    | n + 1 => b + b + n
  a + a

/--
info: innerHave.eq_1 :
  innerHave 0 =
    have a :=
      have b := 0 * 0 + 0;
      b;
    a + a
-/
#guard_msgs in #check innerHave.eq_1

/--
info: innerHave.eq_2 (n : Nat) :
  innerHave n.succ =
    have a :=
      have b := n.succ * n.succ + n.succ;
      b + b + n;
    a + a
-/
#guard_msgs in #check innerHave.eq_2

-- 2. The same, with a non-variable discriminant `x + 1`.
def mixedUnderHave (x : Nat) : Nat :=
  have a :=
    have b := x * x
    match x, x + 1 with
    | 0, _ => b
    | n + 1, m => b + b + n + m
  a + a

/--
info: mixedUnderHave.eq_1 :
  mixedUnderHave 0 =
    have a :=
      have b := 0 * 0;
      b;
    a + a
-/
#guard_msgs in #check mixedUnderHave.eq_1

/--
info: mixedUnderHave.eq_2 (n : Nat) :
  mixedUnderHave n.succ =
    have a :=
      have b := n.succ * n.succ;
      b + b + n + (n.succ + 1);
    a + a
-/
#guard_msgs in #check mixedUnderHave.eq_2

-- 3. A `have` that is a discriminant, with a value that depends on the split variable.
def discrDep (x : Nat) : Nat :=
  have k := x * x + x
  match x, k with
  | 0, _ => 1
  | n + 1, m => n + m + m

/-- info: discrDep.eq_1 : discrDep 0 = 1 -/
#guard_msgs in #check discrDep.eq_1

/--
info: discrDep.eq_2 (n : Nat) :
  discrDep n.succ =
    have k := n.succ * n.succ + n.succ;
    n + k + k
-/
#guard_msgs in #check discrDep.eq_2

-- 4. With `cleanup.letToHave false`, the `have` stays a `have`.
def noCleanup (x : Nat) : Nat :=
  have y := x + 1
  y + y

/--
info: noCleanup.eq_1 (x : Nat) :
  noCleanup x =
    have y := x + 1;
    y + y
-/
#guard_msgs in #check noCleanup.eq_1
