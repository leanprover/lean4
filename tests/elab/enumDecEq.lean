inductive Foo1 where
  | a1
  deriving DecidableEq, BEq, Ord, ReflBEq, LawfulBEq, Std.ReflOrd, Std.LawfulEqOrd

inductive Foo2 where
  | a1 | a2
  deriving DecidableEq, BEq, Ord, ReflBEq, LawfulBEq, Std.ReflOrd, Std.LawfulEqOrd

inductive Foo3 where
  | a1 | a2 | a3
  deriving DecidableEq, BEq, Ord, ReflBEq, LawfulBEq, Std.ReflOrd, Std.LawfulEqOrd

inductive Foo4 where
  | a1 | a2 | a3 | a4
  deriving DecidableEq, BEq, Ord, ReflBEq, LawfulBEq, Std.ReflOrd, Std.LawfulEqOrd

inductive Foo5 where
  | a1 | a2 | a3 | a4 | a5
  deriving DecidableEq, BEq, Ord, ReflBEq, LawfulBEq, Std.ReflOrd, Std.LawfulEqOrd

inductive Foo10 where
  | a1 | a2 | a3 | a4 | a5 | a6 | a7 | a8 | a9 | a10
  deriving DecidableEq, BEq, Ord, ReflBEq, LawfulBEq, Std.ReflOrd, Std.LawfulEqOrd
