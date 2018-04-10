namespace foo

  class structA :=
  mk :: (a : nat)

  class structB extends structA :=
  mk :: (b : nat)

  #check @structA.a
  #check @structB.to_structA

end foo
