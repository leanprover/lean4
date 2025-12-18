def foo : Nat := 1

def bar : Nat :=
  let rec foo := 10
  foo.add 1

def baz : Nat :=
  .add foo 1
where
  foo := 10

def bar2 : Nat :=
  foo.add 1
where
  foo := 10

/--
info: 11
-/
#guard_msgs in
#eval bar -- 11
/--
info: 11
-/
#guard_msgs in
#eval baz -- 11
/--
info: 11
-/
#guard_msgs in
#eval bar2

def bla.aux := 1
def bla : Nat → Nat
 | n => n + bla.aux -- should not be interpreted as `(bla).aux`

/--
info: 4
-/
#guard_msgs in
#eval bla 3

def boo : Nat :=
  let n := 0
  n.succ + (m |>.succ) + m.succ
where
  m := 1

example : boo = 5 := rfl
