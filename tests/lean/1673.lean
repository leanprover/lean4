def foo.a (n: Nat):
  ¬ True
:=
  fun nope => (foo.a n) nope
