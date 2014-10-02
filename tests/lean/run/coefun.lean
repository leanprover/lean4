inductive obj (A : Type) :=
mk : A → obj A

inductive fn (A B : Type) :=
mk : (obj A → obj B) → fn A B

definition to_fun [coercion] {A B : Type} (f : fn A B) : obj A → obj B :=
fn.rec (λf, f) f

constant n : Type.{1}
constant f : fn n n
constant a : obj n
check (f a)
