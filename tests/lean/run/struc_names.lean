namespace foo

  structure [class] structA :=
  mk :: (a : nat)

  structure [class] structB extends structA :=
  mk :: (b : nat)

  #check @structA.a
  #check @structB.to_structA

end foo
