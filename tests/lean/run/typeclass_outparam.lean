#exit

class OPClass (α : outParam Type) (β : Type) : Type := (u : Unit := ())

instance op₁ : OPClass Nat Nat := {}

#synth OPClass Nat Nat
