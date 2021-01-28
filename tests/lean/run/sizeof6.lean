import Std

inductive Foo where
  | mk (args : Std.PersistentArray Foo)

#print Foo.mk.sizeOf_spec
#print Foo._sizeOf_2_eq
#print Foo._sizeOf_3_eq
