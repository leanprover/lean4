--javra:        Maybe this should go somewhere else

open eq
inductive tdecidable [class] (A : Type) : Type :=
inl :  A → tdecidable A,
inr : ~A → tdecidable A

structure decidable_paths [class] (A : Type) :=
(elim : ∀(x y : A), tdecidable (x = y))
