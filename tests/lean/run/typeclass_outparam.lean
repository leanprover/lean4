

class OPClass (α : outParam Type) (β : Type) : Type := (u : Unit := ())

instance op₁ : OPClass Nat Nat := {}

set_option pp.all true

/-- info: op₁ -/
#guard_msgs in
#synth OPClass Nat Nat
