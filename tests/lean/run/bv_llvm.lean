import Std.Tactic.BVDecide

theorem remAnd_a_thm (x : _root_.BitVec 32) :
    x + x.sdiv 8#32 * 4294967288#32 &&& 1#32 = x &&& 1#32 := by
  bv_decide

theorem test21_thm (x : _root_.BitVec 8) :
    x.sshiftRight 7 &&& 1#8 = x >>> 7 := by
  bv_decide

theorem bitvec_AndOrXor_1683_2 : ∀ (a b : BitVec 64), (b ≤ a) || (a != b) = true := by
  intros; bv_decide

theorem short_circuit_mul_right (x x_1 : BitVec 32) (h : ¬x_1 &&& 4096#32 == 0#32) :
    (x ||| 4096#32) * (x ||| 4096#32) = (x ||| x_1 &&& 4096#32) * (x ||| 4096#32) := by
  bv_decide

theorem short_circuit_mul_left (x x_1 : BitVec 32) (h : ¬x_1 &&& 4096#32 == 0#32) :
    (x ||| 4096#32) * (x ||| 4096#32) = (x ||| 4096#32) * (x ||| x_1 &&& 4096#32) := by
  bv_decide

theorem short_circuit_triple_mul (x x_1 x_2 : BitVec 32) (h : ¬x_2 &&& 4096#32 == 0#32) :
    (x_1 ||| 4096#32) * x * (x_1 ||| 4096#32) = (x_1 ||| x_2 &&& 4096#32) * x * (x_1 ||| 4096#32) := by
  bv_decide
