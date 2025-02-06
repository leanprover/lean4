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
error: don't know how to synthesize implicit argument 'α'
  @f ?_ Nat x Nat.zero
context:
⊢ Type
---
error: failed to infer definition type
-/
#guard_msgs in
example :=
  f (y := Nat.zero)
