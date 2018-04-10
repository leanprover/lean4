open nat
namespace foo
section
  parameter (X : Type)
  definition A {n : ℕ} : Type := X
  variable {n : ℕ}
  set_option pp.implicit true
  #check @A n
  set_option pp.full_names true
  #check @foo.A n
  #check @A n

  set_option pp.full_names false
  #check @foo.A n
  #check @A n
end
end foo
