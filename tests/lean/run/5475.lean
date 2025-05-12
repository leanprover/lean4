/-!
# Eta arguments had wrong context in "don't know how to synthesize implicit" errors
https://github.com/leanprover/lean4/issues/5475
-/

set_option pp.mvars false

/-!
Formerly, argument `x` appeared as `_fvar.123`
-/

def f {α β : Type} (x: α) (y: β) : α := x
/--
error: Failed to infer definition type.

Partial assignment
  ?_ → ?_

context:
⊢ Type
---
error: Implicit argument could not be inferred in application of `f`.

The argument `α` is not determined by the other arguments or the expected type in
  @f ?_ Nat x Nat.zero

context:
⊢ Type
-/
#guard_msgs in
example :=
  f (y := Nat.zero)
