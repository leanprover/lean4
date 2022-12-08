inductive Foo1 where
  | a1
  deriving DecidableEq

#print Foo1.ofNat

inductive Foo2 where
  | a1 | a2
  deriving DecidableEq

#print Foo2.ofNat

inductive Foo3 where
  | a1 | a2 | a3
  deriving DecidableEq

#print Foo3.ofNat

inductive Foo4 where
  | a1 | a2 | a3 | a4
  deriving DecidableEq

#print Foo4.ofNat

inductive Foo5 where
  | a1 | a2 | a3 | a4 | a5
  deriving DecidableEq

#print Foo5.ofNat
