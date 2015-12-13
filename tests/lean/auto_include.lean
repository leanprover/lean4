import algebra.group
open algebra

section
variables {A : Type} [group A]
variables {B : Type} [group B]

definition foo (a b : A) : a * b = b * a :=
sorry

definition bla (b : B) : b * 1 = b :=
sorry

print foo
print bla
end

section
variable {A : Type}
variable [group A]
variable {B : Type}
variable [group B]

definition foo2 (a b : A) : a * b = b * a :=
sorry

definition bla2 (b : B) : b * 1 = b :=
sorry

print foo2
print bla2
end
