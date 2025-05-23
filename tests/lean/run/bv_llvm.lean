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


#eval BitVec.umulOverflow (15#4) (14#4) ↔ (((BitVec.zeroExtend 5 (15#4)) * (BitVec.zeroExtend 5 (14#4))).getLsbD 4 || BitVec.resRec (15#4) (14#4) 0 (by omega) (by omega))

open BitVec

def test : IO Unit := do
  have w := 5
  let mut success : Bool := true
  for xx in [0 : 2^w] do
    for yy in [0 : 2^w] do
      have x := BitVec.ofNat w xx
      have y := BitVec.ofNat w yy
      have : 1 < w := by sorry
      have f :=  decide (((zeroExtend (w + 1) x) * (zeroExtend (w + 1) y)).getLsbD w || resRec x y (w - 1) (by omega) (by omega) (by omega))
      have g :=  decide (umulOverflow x y)
      -- have h :=  decide ((((zeroExtend (w + 1) x) * (zeroExtend (w + 1) y)).getLsbD w ))
      -- -- | i + 1 => (resRec x y i (by omega) (by omega)) || (aandRec x y (i + 1) (by omega))
      -- have k :=  decide ((aandRec x y (w - 1) (by omega) ))
      -- have j :=  decide ((aandRec x y (w - 2) (by omega)))
      -- -- y[s] && uppcRec x s (by omega), s = w - 2
      -- have m :=  decide ((y[w - 2]))
      -- -- | i + 1 =>  x.getLsbD (i + 1) || uppcRec x i (by omega) -- there is one redundant case here
      -- have n :=  decide ((uppcRec x (w - 2) (by omega)))
      -- have o :=  decide ((x.getLsbD (w - 2)))
      -- have p :=  decide ((uppcRec x (w - 3) (by omega)))
      -- have l :=  decide ((resRec x y (w - 3) (by omega) (by omega)))

      IO.print f!"fastUmulOverflow {x.toNat} {y.toNat} = {f}\t"
      IO.print f!"umulOverflow x y = {g}\t"
      if g ≠ f then do
        IO.print f!"  FAIL"
        success := false
      IO.println ""
    IO.println ""
  IO.println s!"success? {success}"


#eval! test
