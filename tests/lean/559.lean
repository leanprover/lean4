import algebra.ordered_field
open algebra
section sequence_c

  parameter Q : Type
  parameter lof_Q : linear_ordered_field Q
  definition to_lof [instance] : linear_ordered_field Q := lof_Q
  include to_lof

  theorem foo (a b : Q) : a + b = b + a := !add.comm

end sequence_c
