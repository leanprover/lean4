inductive {u} one1 : Type (max 1 u)
| unit : one1

set_option pp.universes true
#check one1

inductive {u} one2 : Type (max 1 u)
| unit : one2

#check one2

section foo
  universe u2
  parameter A : Type u2

  inductive {u} wrapper : Type (max 1 u u2)
  | mk : A → wrapper
  #check wrapper
end foo

#check wrapper
