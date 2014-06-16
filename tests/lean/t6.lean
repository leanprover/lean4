definition Bool : Type.{1} := Type.{0}
section
  {parameter} A : Type  -- Mark A as implicit parameter
  parameter   R : A → A → Bool
  definition  id (a : A) : A := a
  definition  refl : Bool := forall (a : A), R a a
  definition  symm : Bool := forall (a b : A), R a b -> R b a
end
check id.{2}
check refl.{1}
check symm.{1}

