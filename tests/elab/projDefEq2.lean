structure Foo where
  x : Nat
  h : x > 1

theorem foo_gt_0 (foo : Foo) : foo.x > 0 :=
  Nat.lt_of_succ_lt foo.h

example (x : Nat) (h : x > 1) : id { x, h : Foo }.x > 0 :=
  foo_gt_0 { x, h }

example (x : Nat) (h : x > 1) : id { x, h : Foo }.x > 0 :=
  foo_gt_0 _
