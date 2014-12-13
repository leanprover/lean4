namespace foo

  structure structA [class] :=
  mk :: (a : nat)

  structure structB [class] extends structA :=
  mk :: (b : nat)

  check @structA.a
  check @structB.to_structA

end foo
