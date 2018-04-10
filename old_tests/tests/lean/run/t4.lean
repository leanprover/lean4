namespace foo
  definition {u} f (A : Type u) : Type u := A
  #check f.{1}
end foo

constant N : Type
section
  variable A : Type*
  definition g (a : A) (B : Type*) : A := a
  #check g.{_ 2}
end
#check g.{2 3}
