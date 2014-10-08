import logic

definition subsingleton (A : Type) := ∀⦃a b : A⦄, a = b
class subsingleton

protected definition prop.subsingleton [instance] (P : Prop) : subsingleton P :=
λa b, !proof_irrel
