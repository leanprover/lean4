structure foo :=
(x : nat) (y : nat) (z : bool)

#check let s := {foo . x := let v1 := 10 + 10 + 20 + 30 + 40 + 10 + 20 + 30 + 40 + 50 + 10 + 10, v2 := 10 + 10 + 10 + 10 + 10 + 10 + 10 + 10 + 10 + 10 + 20, v3 := 10 + 10 + 10 + 10 + 10 + 10 + 10 + 10 + 10 + 10 + 20, v4 := 10 + 10 + 10 + 10 + 10 + 10 + 10 + 10 + 10 + 10 + 20 in v1 + v2 + v3 + v4, y := 20, z := tt} in s^.x + s^.y

set_option pp.structure_instances_qualifier true

#check let s := {foo . x := let v1 := 10 + 10 + 20 + 30 + 40 + 10 + 20 + 30 + 40 + 50 + 10 + 10, v2 := 10 + 10 + 10 + 10 + 10 + 10 + 10 + 10 + 10 + 10 + 20, v3 := 10 + 10 + 10 + 10 + 10 + 10 + 10 + 10 + 10 + 10 + 20, v4 := 10 + 10 + 10 + 10 + 10 + 10 + 10 + 10 + 10 + 10 + 20 in v1 + v2 + v3 + v4, y := 20, z := tt} in s^.x + s^.y

set_option pp.structure_instances false

#check {foo . x := 10, y := 20, z := ff}

set_option pp.structure_instances true

#check {foo . x := 10, y := 20, z := ff}

set_option pp.structure_instances_qualifier false

#check {foo . x := 10, y := 20, z := ff}

#check {foo . x := 10, y := 20, z := ff}^.x

#check (1, 2).1

constant boo : nat → nat → nat × nat

#check (boo 1 1)^.fst

structure F :=
(fn : nat → nat → nat)
(v  : nat)

constant h : nat → F

#check (h 0)^.fn 10 20
