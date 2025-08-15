import Std.Tactic.BVDecide

def test : IO Unit :=
  have w := 5
  for xx in [0 : 2^w] do
    have x := BitVec.ofNat w xx
    let mut pop := 0
    for bit in [0 : w] do
      if x.getLsbD bit = true then pop := pop + 1

    IO.print f!"sum of set bits is {pop} = {x.popCountParSum}"
    if pop ≠ x.popCount then
      IO.println "FAIL"
    else
      IO.println " OK"


    IO.println ""

#eval test
