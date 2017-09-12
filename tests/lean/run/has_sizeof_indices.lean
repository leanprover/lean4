universes u

inductive foo : nat → Type
| baz (n : nat) : foo n → foo (nat.succ n)

lemma foo.size (α β : Type u) (n a : ℕ) : has_sizeof (foo a) :=
by tactic.mk_has_sizeof_instance

inductive bla : nat → bool → Type
| mk : bla 0 ff
| baz (n : nat) : bla n ff → bla (nat.succ n) tt
| boo (n : nat) : bla n tt → bla (nat.succ n) ff

lemma bla.size (α β : Type u) (a : ℕ) (t : bool)  : has_sizeof (bla a t) :=
by tactic.mk_has_sizeof_instance
