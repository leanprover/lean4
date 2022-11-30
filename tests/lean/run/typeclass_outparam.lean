

class OPClass (α : OutParam Type) (β : Type) : Type := (u : Unit := ())

instance op₁ : OPClass Nat Nat := {}

set_option pp.all true

#synth OPClass Nat Nat
