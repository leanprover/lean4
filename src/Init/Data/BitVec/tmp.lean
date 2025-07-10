import Init.System.IO
import Init.Data.BitVec


open BitVec

      set_option diagnostics true


def test : IO Unit := do
  let w := 4
  for xx in [0 : 2^w] do
    let x := BitVec.ofNat w xx
    let mut pop : Nat := 0
    for kk in [0:w] do
      if x.getLsbD kk = false then pop := pop
        else pop := pop + 1
    let bbpop : BitVec w := x.popCountParSum
    let bvpop : BitVec w := x.popCount
    -- IO.print f!"\nNaive popCount returned {pop}, bitblaster circuit returned{bbpop}, bvPop returned {bvpop}"
    if bbpop.toNat ≠ pop then IO.print f!"\nFAIL"

    IO.println ""

#eval! test


-- when 0 ≤ x.toInt and y.toInt < 0
-- 2# emod -4 = 2
-- 2# fmod -4 = -2
-- fmod = y + emod
