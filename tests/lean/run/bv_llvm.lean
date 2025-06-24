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
  bv_decide +shortCircuit

theorem short_circuit_mul_left (x x_1 : BitVec 32) (h : ¬x_1 &&& 4096#32 == 0#32) :
    (x ||| 4096#32) * (x ||| 4096#32) = (x ||| 4096#32) * (x ||| x_1 &&& 4096#32) := by
  bv_decide +shortCircuit

theorem short_circuit_triple_mul (x x_1 x_2 : BitVec 32) (h : ¬x_2 &&& 4096#32 == 0#32) :
    (x_1 ||| 4096#32) * x * (x_1 ||| 4096#32) = (x_1 ||| x_2 &&& 4096#32) * x * (x_1 ||| 4096#32) := by
  bv_decide +acNf +shortCircuit

#check BitVec.zero_srem

def msb_srem (x y : BitVec w) :=
    (x.msb && decide (x.srem y ≠ 0)) -- if ¬ y.msb || (x.dvd y) then ¬ x.smod y, else true

-- def msb_smod (x y : BitVec w) :=
--   (x.msb && y = 0) || (y.msb && ¬ (x.smod y) = 0)
#check BitVec.toFin_neg
def test : IO Unit :=
  have w := 4
  for xx in [0 : 2^w] do
    for yy in [0 : 2^w] do
      have x := BitVec.ofNat w xx
      have y := BitVec.ofNat w yy

      IO.print f!"{x.toInt} srem {y.toInt} = {(x.srem y).toInt} "

      if msb_srem x y ≠ (x.srem y).msb then
        IO.println "FAIL"

      if (msb_srem x y) then
        IO.println "\t- "
      else
        IO.println "\t  "
    IO.println ""

#check BitVec.srem

#eval test
