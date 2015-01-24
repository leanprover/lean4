section foo
  parameter A : Type
  variable a : A
  definition foo := a

  check foo

  structure point [class] :=
  (x : A) (y : A)
end foo

check foo

definition point_nat [instance] : point nat :=
point.mk nat.zero nat.zero

print classes
check point
