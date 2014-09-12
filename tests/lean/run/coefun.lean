inductive obj (A : Type) :=
mk : A → obj A

inductive fn (A B : Type) :=
mk : (obj A → obj B) → fn A B

definition to_fun [coercion] {A B : Type} (f : fn A B) : obj A → obj B :=
fn.rec (λf, f) f

variable n : Type.{1}
variable f : fn n n
variable a : obj n
check (f a)
