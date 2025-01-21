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

--example (b : Basic) : b.x + b.y = 0 := by
example (b : Basic) : b.x + b.y = 0 := by
  -- TODO: with this it works, figure out where i'm messing up mvar contexts
  -- bv_normalize
set_option trace.Meta.Tactic.bv true in
set_option trace.Meta.Tactic.simp.rewrite true in
set_option trace.profiler true in
  bv_normalize
  sorry
  --bv_decide

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
  h : x + y = 0

example (p : Param x y) : x + y = 0 := by
  bv_decide

end Ex5
