@[derive [decidable_eq, inhabited, has_sizeof]]
inductive foo
| bar : ℕ → foo
| baz : foo

#check foo.decidable_eq
#check foo.inhabited
#check foo.has_sizeof
