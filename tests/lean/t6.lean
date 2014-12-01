prelude definition Prop : Type.{1} := Type.{0}
section
  variable    {A : Type}  -- Mark A as implicit parameter
  variable    R : A → A → Prop
  definition  id (a : A) : A := a
  definition  refl : Prop := forall (a : A), R a a
  definition  symm : Prop := forall (a b : A), R a b -> R b a
end
check id.{2}
check refl.{1}
check symm.{1}
