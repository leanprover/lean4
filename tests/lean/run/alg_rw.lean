import algebra.group
open algebra

section
  variable {A : Type}
  variable [s : comm_monoid A]
  include s

  theorem one_mul_one : 1 * 1 = (1:A) :=
  mul_one 1
end

section
  variable {A : Type}
  variable [s : comm_group A]
  include s

  theorem one_mul_one2 : (one : A) * 1 = 1 :=
  by rewrite one_mul_one
end
