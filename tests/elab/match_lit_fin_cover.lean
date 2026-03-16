/-
Test for match-expression when we cover all possible
values of a `Fin` or `BitVec` type.
-/

def boo (x : Fin 3) : Nat :=
  match x with
  | 0 => 1
  | 1 => 2
  | 2 => 4

@[simp] def bla (x : Fin 3) (y : Nat) : Nat :=
  match x, y with
  | 0, _   => 10
  | 1, _   => 20
  | 2, 0   => 30
  | 2, y+1 => bla x y + 1

/--
info: bla.eq_1 (y : Nat) : bla 0 y = 10
-/
#guard_msgs in
#check bla.eq_1

/-- info: bla.eq_4 (y_2 : Nat) : bla 2 y_2.succ = bla 2 y_2 + 1 -/
#guard_msgs in
#check bla.eq_4

open BitVec

def foo (x : BitVec 3) : Nat :=
  match x with
  | 0b000#3 => 7
  | 0b001#3 => 6
  | 0b010#3 => 5
  | 0b011#3 => 4
  | 0b100#3 => 3
  | 0b101#3 => 2
  | 0b110#3 => 1
  | 0b111#3 => 0

def foo' (x : BitVec 3) (y : Nat) : Nat :=
  match x, y with
  | 0b000#3, _   => 7
  | 0b001#3, _   => 6
  | 0b010#3, _   => 5
  | 0b011#3, _   => 4
  | 0b100#3, _   => 3
  | 0b101#3, _   => 2
  | 0b110#3, _   => 1
  | 0b111#3, 0   => 0
  | 0b111#3, y+1 => foo' 7 y + 1

attribute [simp] foo'

/--
info: foo'.eq_1 (y : Nat) : foo' (0#3) y = 7
-/
#guard_msgs in
#check foo'.eq_1

/--
info: foo'.eq_2 (y : Nat) : foo' (1#3) y = 6
-/
#guard_msgs in
#check foo'.eq_2

/-- info: foo'.eq_9 (y_2 : Nat) : foo' (7#3) y_2.succ = foo' 7 y_2 + 1 -/
#guard_msgs in
#check foo'.eq_9
