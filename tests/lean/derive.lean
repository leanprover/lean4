@[derive [decidable_eq, inhabited, has_sizeof]]
inductive foo (α β : Type*)
| bar : ℕ → foo
| baz : foo → α → foo

#check foo.decidable_eq
#check foo.inhabited
#check foo.has_sizeof
