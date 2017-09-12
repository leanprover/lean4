@[derive [decidable_eq, inhabited, has_reflect, has_sizeof]]
inductive foo (α β : Type*)
| bar : ℕ → foo
| baz : foo → α → foo

#check foo.decidable_eq
#check foo.inhabited
#check foo.has_reflect
#check foo.has_sizeof

-- indexed families

@[derive decidable_eq]
inductive {u} foo' (α β : Type u) (n : nat) : nat → Type u
| bar : ℕ → foo' 0
| baz (n : nat) : foo' n → α → foo' (nat.succ n)

#check foo'.decidable_eq
