import algebra.group
open tactic

example (A : Type) [semigroup A] (a b c : A) : (a * b) * c = a * (b * c) :=
by mk_const `mul.assoc >>= apply

example (A : Type) [semigroup A] (a b c : A) : (a * b) * c = a * (b * c) :=
by to_expr `(@mul.assoc) >>= apply

example (A : Type) [semigroup A] (a b c : A) : (a * b) * c = a * (b * c) :=
by refine `(mul.assoc _ _ _)

meta_definition lean2_exact (p : pexpr) : tactic unit :=
do t ← target, to_expr `((%%p : %%t)) >>= exact

example (A : Type) [semigroup A] (a b c : A) : (a * b) * c = a * (b * c) :=
by lean2_exact `(mul.assoc _ _ _)
