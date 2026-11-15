import Std.Tactic.BVDecide

/-!
This is a regression test derived from #16224. As described there it turns out that converting
a rfl `BitVec.cast x rfl` to just `x` by defeq is exponential as it forces the kernel to evaluate
`x` which is potentially expensive.
-/

example (z : BitVec 32) :
    0#0 ++ (z + 33554432#32).sshiftRight 26 * 3329#32 =
      (z + 33554432#32).sshiftRight 26 * 3329#32 := by
  bv_normalize

example (z : BitVec 32) :
    ((z + 33554432#32).sshiftRight 26 * 3329#32) >>> 0 =
      (z + 33554432#32).sshiftRight 26 * 3329#32 := by
  bv_normalize

example (x : BitVec 16) :
    BitVec.setWidth 8
        (BitVec.setWidth 16
            (BitVec.signExtend 32 x -
              (20159#32 * BitVec.signExtend 32 x + 33554432#32).sshiftRight 26 * 3329#32) >>> 0) =
      BitVec.setWidth 8
        (BitVec.setWidth 16
          (BitVec.signExtend 32 x -
            (20159#32 * BitVec.signExtend 32 x + 33554432#32).sshiftRight 26 * 3329#32)) := by
  bv_decide
