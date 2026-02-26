class Foo (α : Type) where x : α

instance : CoeSort (Foo α) Type where
  coe _ := α

#check @id (Foo.mk ()) ()
