section foo
  parameter A : Type
  variable a : A
  definition foo := a

  #check foo

  class point :=
  (x : A) (y : A)
end foo

#check foo

attribute [instance]
definition point_nat : point nat :=
point.mk nat.zero nat.zero

#print classes
#check point
