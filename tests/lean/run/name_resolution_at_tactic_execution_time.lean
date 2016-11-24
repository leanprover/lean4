structure Foo : Type := (foo : ℕ)
open Foo
set_option pp.all true

example (P : Prop) : P → P
| foo := by exact foo

example (P : Prop) : P → P
| bla :=
  begin
    rename bla foo,
    exact foo
  end

example (f : Foo) : nat :=
by exact foo f
