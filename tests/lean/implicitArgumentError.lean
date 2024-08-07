/-!
In the past, when an implicit argument couldn't be synthesized, the name of the argument got lost during elaboration.
Now it is saved and added to the error message.

In this exaple, that is 'n'.
-/

def foo {n : Nat} := 2*n

set_option pp.mvars false

/--
error: don't know how to synthesize implicit argument 'n'
  @foo ?_
context:
⊢ Nat
-/
#guard_msgs in
#eval foo
