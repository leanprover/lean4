constant f : nat → nat

namespace foo
axiom fax : ∀ x, f x = x
end foo

attribute [simp] foo.fax

example (a : nat) : f a = a :=
by simp -- works

example (a : nat) : f a = a :=
by simp [-fax] -- Error: unknown identifier 'fax'

example (a : nat) : f a = a :=
by simp [-foo.fax] -- Error: simplify failed to simplify

section
open foo
example (a : nat) : f a = a :=
by simp [-fax] -- Error: simplify failed to simplify
end

example (a : nat) (h : a = 0) : a = 0 :=
by simp [-h] -- Error: invalid local exception h, '*' was not used

example (a : nat) (h : a = 0) : a = 0 :=
by simp [*, -h] -- Error: simplify failed to simplify

example (a : nat) (h : a = 0) : a = 0 :=
by simp [*] -- works

example (a b : nat) (h : b = 0) (h₁ : a = b) (h₂ : b = a) : b = 0 :=
by simp [*, -h₁, -h₂] -- we can prevent loops by removing "bad" hypotheses
