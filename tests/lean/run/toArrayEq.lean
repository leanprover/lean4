inductive Foo
  | foo : Nat → Foo
  | foos : Array Foo → Foo
  deriving BEq

example : Foo.foo 0 ≠ Foo.foo 1 := by simp

example : #[0] ≠ #[1] := by simp

example : #[Foo.foo 0] ≠ #[Foo.foo 1] := by simp

example : Foo.foos #[.foo 0] ≠ Foo.foos #[.foo 1] := by simp
