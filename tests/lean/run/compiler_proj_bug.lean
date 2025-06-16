structure S :=
(a : Nat) (h : a > 0) (b : Nat)

def f (s : S) :=
s.b - s.a

/--
info: 25
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
#eval! f {a := 5, b := 30, h := sorry }
