def int' := int

#eval id_rhs int' (-1 : ℤ)
-- #2147483647

instance : has_repr int' :=
by unfold int'; apply_instance

#eval id_rhs int' (-1 : ℤ)
-- -1

@[reducible] def int'' := int

/- Don't need to define has_repr instance for int'' because it is reducible -/
#eval id_rhs int'' (-1 : ℤ)
-- -1

inductive foo
| mk₁ : bool → foo
| mk₂ : bool → foo

#eval foo.mk₁ tt
