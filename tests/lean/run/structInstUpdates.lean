structure A where
  x : Nat := 0

structure B extends A where
  y : Nat := 0

structure C extends B where
  z : Nat := 0

variable (c : C)

/-- info: { x := 1, y := c.y, z := c.z } : C -/
#guard_msgs in #check { c with x := 1 }
/-- info: { toA := c.toA, y := 1, z := c.z } : C -/
#guard_msgs in #check { c with y := 1 }
/-- info: { toB := c.toB, z := 1 } : C -/
#guard_msgs in #check { c with z := 1 }
