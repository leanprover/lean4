import data.int
open int

constant f : int → int

definition double (x : int) := x + x

theorem tst1 (x y : int) (H1 : double x = 0) (H2 : double y = 0) (H3 : f (double y) = 0) (H4 : y > 0) : f (x + x) = 0 :=
by rewrite [↑double at H1, H1, H2 at H3, H3]
