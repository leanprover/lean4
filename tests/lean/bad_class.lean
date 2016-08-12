--
namespace foo
definition subsingleton (A : Type) := ∀⦃a b : A⦄, a = b
attribute subsingleton [class]

attribute [instance]
protected definition prop.subsingleton (P : Prop) : subsingleton P :=
λa b, proof_irrel _ _
end foo
