namespace foo
  definition f.{l} (A : Type.{l}) : Type.{l} := A
  check f.{1}
end foo

constant N : Type.{1}
section
  variable A : Type
  definition g (a : A) (B : Type) : A := a
  check g.{_ 2}
end
check g.{2 3}
