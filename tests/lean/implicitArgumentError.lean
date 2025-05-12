/-!
In the past, when an implicit argument couldn't be synthesized, the name of the argument got lost during elaboration.
Now it is saved and added to the error message.

In this example, that is 'n'.
-/

def foo {n : Nat} := 2*n

/--
error: Implicit argument could not be inferred in application of `foo`.

The argument `n` is not determined by the other arguments or the expected type in
  @foo ?_

context:
⊢ Nat
-/
#guard_msgs in
set_option pp.mvars false in
#eval foo
