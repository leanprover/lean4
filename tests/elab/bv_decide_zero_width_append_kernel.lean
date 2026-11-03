import Std.Tactic.BVDecide

/-!
`bv_normalize` rewrites `0#0 ++ x` to `x` with `BitVec.zero_width_append`, whose right-hand side is
`x.cast _`. Without an explicit `BitVec.cast_eq` step the kernel accepts `x.cast _ ≡ x` only by
evaluating `x`, which for the symbolic terms below exhausts memory. A right shift by `0` reaches the
same rewrite via `0#0 ++ extractLsb' 0 w x`.
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
