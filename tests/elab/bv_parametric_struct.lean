import Std.Tactic.BVDecide

/--
The `Byte` type can have any bitwidth `w`. It carries a two's complement integer
value of width `w` and a per-bit poison mask modeling bitwise delayed undefined
behavior.
-/
structure Byte (w : Nat) where
  /-- A two's complement integer value of width `w`. -/
  val : BitVec w
  /-- A per-bit poison mask of width `w`. -/
  poison : BitVec w

def or {w : Nat} (x y : Byte w) : Byte w :=
  ⟨x.val ||| y.val, x.poison ||| y.poison⟩

example (x y : Byte 8) : or x y = or y x := by
  unfold _root_.or
  bv_decide

