class WrappedNat (α : Type) where
  n : Nat

inductive FalseContainer where
  | nat (n : Nat)
  | oops (f : Prop → False)

def f (x : FalseContainer) : WrappedNat FalseContainer :=
  match x with
  | .nat n => { n }
  | .oops f => (f (0 == 0)).rec

/--
info: 1
-/
#guard_msgs in
#eval f (.nat 1) |>.n

