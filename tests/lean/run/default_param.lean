universe variable u

def f (a : nat) (o : opt_param nat 5) :=
a + o

example : f 1 = f 1 5 :=
rfl

#check f 1

structure config :=
(v1   := 10)
(v2   := 20)
(flag := tt)
(ps   := ["hello", "world"])

def g (a : nat) (c : opt_param config {}) : nat :=
if c^.flag then a + c^.v1 else a + c^.v2

example : g 1 = 11 :=
rfl

example : g 1 {flag := ff} = 21 :=
rfl

example : g 1 {v1 := 100} = 101 :=
rfl

def h (a : nat) (c : opt_param config {v1 := a}) : nat :=
g a c

example : h 2 = 4 :=
rfl

example : h 3 = 6 :=
rfl

example : h 2 {flag := ff} = 22 :=
rfl

def boo (a : nat) (b : opt_param nat a) (c : opt_param bool ff) (d : opt_param config {v2 := b, flag := c}) :=
g a d

#check boo 2

example : boo 2 = 4 :=
rfl

example : boo 2 20 = 22 :=
rfl

example : boo 2 0 tt = 12 :=
rfl

open tactic
set_option pp.all true

meta def check_expr (p : pexpr) (t : expr) : tactic unit :=
do e ← to_expr p, guard (t = e)

run_cmd do
  e ← to_expr `(boo 2),
  check_expr `(boo 2 (2:nat) ff {v1 := config.v1._default, v2 := 2, flag := ff, ps := config.ps._default}) e,
  e ← to_expr `(f 1),
  check_expr `(f 1 (5:nat)) e
