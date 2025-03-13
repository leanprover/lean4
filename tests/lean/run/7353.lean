structure Foo where
  obj : Unit → Type
  map : obj ()

def foo : Foo where
  obj _ := Function.const (() = ()) Nat (id rfl)
  map := id (0 : Nat)

set_option pp.proofs true
set_option pp.explicit true

/--
info: def foo : Foo :=
Foo.mk (fun x => @Function.const Type (@Eq Unit Unit.unit Unit.unit) Nat foo.proof_1)
  (@id ((fun x => @Function.const Type (@Eq Unit Unit.unit Unit.unit) Nat foo.proof_1) Unit.unit)
    (@OfNat.ofNat Nat 0 (instOfNatNat 0)))
-/
#guard_msgs in
#print foo
