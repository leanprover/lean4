@[class] axiom OPClass (α : outParam Type) (β : Type) : Type

@[instance] axiom op₁ : OPClass Nat Nat

#synth OPClass Bool Nat
