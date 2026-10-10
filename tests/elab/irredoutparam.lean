class Foo (α : Type) (β : outParam Type) where

def Bar :=
  Nat

instance : Foo Nat Nat where

/--
error: failed to synthesize
  Foo Nat Bar

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth Foo Nat Bar -- instFooNat
