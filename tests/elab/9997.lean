/-!
# `symm` should handle typeclass arguments

https://github.com/leanprover/lean4/issues/9997
-/

/-!
In this example, it used to be that the `example` would have the
"(kernel) declaration has metavariables" error.
-/

axiom Foo : Prop
attribute [class] Foo

axiom R : Nat → Nat → Prop
@[symm]
axiom R.symm [Foo] {n m} : R n m → R m n

example [Foo] {n m} (h : R n m) : R m n := by
  symm
  exact h


/-!
Has a tactic error if it's not able to synthesize the instance.
-/

/--
error: failed to synthesize
  Foo

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
example {n m} (h : R n m) : R m n := by
  symm

/-!
Has errors for symm lemmas that have arguments that can't be synthesized at all.
-/

axiom R' : Nat → Nat → Prop
@[symm]
axiom R'.symm (x : Bool) {n m} : R' n m → R' m n

/--
error: unsolved goals
case x
n m : Nat
⊢ Bool
-/
#guard_msgs in
example {n m} : R' m n := by
  symm
