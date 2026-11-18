import Lean

/-!
Tests for literal evaluation of `BitVec.ofNatClamp` in `simp`/`seval`, in `sym => simp` (via
`Sym.Simp.evalGround`) and in `sym => dsimp` (via `Sym.DSimp.evalGround`), plus basic sanity
checks of the `ofNatClamp` theory.
-/

/-! ## `simp` -/

#check_simp BitVec.ofNatClamp 8 5 ~> 5#8
#check_simp BitVec.ofNatClamp 8 255 ~> 255#8
#check_simp BitVec.ofNatClamp 8 256 ~> 255#8
#check_simp BitVec.ofNatClamp 8 300 ~> 255#8
#check_simp BitVec.ofNatClamp 0 3 ~> 0#0

example : BitVec.ofNatClamp 8 300 = 255#8 := by simp only [seval]

register_sym_simp clampGround where
  post := ground

example : BitVec.ofNatClamp 8 300 = 255#8 := by
  sym => simp clampGround

example (x : BitVec 8) (h : x = 255#8) : x = BitVec.ofNatClamp 8 300 := by
  sym =>
    dsimp
    exact h

example (x : BitVec 12) : BitVec.ofNatClamp 12 x.toNat = x := by simp
