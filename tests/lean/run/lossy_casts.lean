import Std
/-!
Ensure that we have not created lossy cast instances.
-/

/--
error: Type mismatch
  x
has type
  Nat
but is expected to have type
  Fin 8
-/
#guard_msgs in
example (x : Nat) : Fin 8 := x

/--
error: Type mismatch
  x
has type
  Nat
but is expected to have type
  UInt8
-/
#guard_msgs in
example (x : Nat) : UInt8 := x

/--
error: Type mismatch
  x
has type
  Nat
but is expected to have type
  USize
-/
#guard_msgs in
example (x : Nat) : USize := x

/--
error: Type mismatch
  x
has type
  Nat
but is expected to have type
  Int8
-/
#guard_msgs in
example (x : Nat) : Int8 := x

/--
error: Type mismatch
  x
has type
  Nat
but is expected to have type
  ISize
-/
#guard_msgs in
example (x : Nat) : ISize := x

-- TODO: currently there is a global lossy instance `NatCast (BitVec w)`, that should be removed.
