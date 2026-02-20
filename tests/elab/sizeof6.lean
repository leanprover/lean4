import Lean.Data.PersistentArray

inductive Foo where
  | mk (args : Lean.PersistentArray Foo)

#print Foo.mk.sizeOf_spec
#print Foo._sizeOf_2_eq
#print Foo._sizeOf_3_eq
