@[derive has_reflect]
inductive foo (α β : Type*)
| bar : ℕ → foo
| baz : foo → α → foo

#check foo.has_reflect

-- indexed families

@[derive [decidable_eq, has_sizeof]]
inductive {u} foo' (α β : Type u) (n : nat) : nat → Type u
| bar : ℕ → foo' 0
| baz (n : nat) : foo' n → α → foo' (nat.succ n)

#check foo'.decidable_eq
#check foo'.has_sizeof
