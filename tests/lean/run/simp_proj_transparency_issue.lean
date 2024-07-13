structure Foo where
  x : Nat
  y : Nat := 10

attribute [class] Foo

@[instance]
def f (x : Nat) : Foo :=
  { x := x + x }

@[instance]
def g (x : Nat) : Foo :=
  { x := x + x }

opaque q : Nat → Prop

example (h : q (f x).1) : q (g x).1 := by
  -- Projections must not bump transparency setting from `reducible` to `instances`
  -- Thus, the following tactic must fail
  fail_if_success simp [h]
  assumption
