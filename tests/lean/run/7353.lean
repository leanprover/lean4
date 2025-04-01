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
{ obj := fun x => @Function.const Type (@Eq Unit Unit.unit Unit.unit) Nat foo._proof_1,
  map :=
    @id (@Function.const Type (@Eq Unit Unit.unit Unit.unit) Nat foo._proof_1) (@OfNat.ofNat Nat 0 (instOfNatNat 0)) }
-/
#guard_msgs in
#print foo
