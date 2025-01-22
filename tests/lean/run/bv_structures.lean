import Std.Tactic.BVDecide

namespace Ex1

structure Basic where
  x : BitVec 32
  y : BitVec 32

example (b : Basic) : b.x + b.y = b.y + b.x := by
  bv_decide

end Ex1

namespace Ex2

structure Basic where
  x : BitVec 32
  y : BitVec 32
  h : y + x = 0

example (b : Basic) : b.x + b.y = 0 := by
  bv_decide

end Ex2

namespace Ex3

structure Recursive where
  x : BitVec 32
  foo : Recursive

-- Don't get fooled by recursive structures
example (_r : Recursive) (a b : BitVec 8) : a + b = b + a := by
  bv_decide

end Ex3

namespace Ex4

structure Foo where
  x : BitVec 32
  y : BitVec 32
  h : x + y = 0

structure Bar extends Foo where
  z : BitVec 32

structure FooBar extends Bar where
  a : Unit

example (f : FooBar) (h : f.z > 0) : f.x + f.y + f.z > 0 := by
  bv_decide

end Ex4

namespace Ex5

structure Param (x : BitVec 32) (y : BitVec 32) where
  h : y + x = 0

example (x y : BitVec 32) (p : Param x y) : x + y = 0 := by
  bv_decide

end Ex5

namespace Ex6

structure Pair where
  x : BitVec 32
  y : BitVec 32

example (a b : Pair) (h1 : a.x = a.y) (h2 : b.x = b.y) (h3 : a.x = b.y) : a = b := by
  bv_decide

example (a b : Pair) (h : a = b) : a.x = b.x := by
  bv_decide

end Ex6

namespace Ex7

structure Single where
  z : BitVec 32

structure Pair where
  x : BitVec 32
  y : Single

example (a b : Pair) (h1 : a.x = a.y.z) (h2 : b.x = b.y.z) (h3 : a.x = b.y.z) : a = b := by
  bv_decide

example (a b : Pair) (h : a = b) : a.x = b.x ∧ a.y.z = b.y.z := by
  bv_decide

end Ex7

namespace Ex8

structure Single where
  z : BitVec 32

structure Pair extends Single where
  x : BitVec 32

example (a b : Pair) (h1 : a.x = a.z) (h2 : b.x = b.z) (h3 : a.x = b.z) : a = b := by
  bv_decide

example (a b : Pair) (h : a = b) : a.x = b.x ∧ a.z = b.z := by
  bv_decide

end Ex8
