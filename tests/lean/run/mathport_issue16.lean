class Foo (α : Type) where x : α

instance : CoeSort (Foo α) Type where
  coe _ := α

instance coeSortToCoe [inst : CoeSort α β] : Coe α β where
  coe := inst.coe

#check @id (Foo.mk ()) ()
