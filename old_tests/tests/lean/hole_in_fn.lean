
inductive foo
| mk : (nat → nat) → foo

definition f : foo :=
foo.mk (λ n, _)
