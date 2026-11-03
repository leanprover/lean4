import Lean

/-! The instances recorded by `Sym.Arith` classification are well typed. -/

open Lean Meta Sym Arith

run_meta do
  for type in [mkConst ``Int, mkConst ``Rat, mkConst ``Nat] do
    SymM.run do
      discard <| classify? type
      for ring in (← getArithState).rings do
        for inst in [ring.ringInst, ring.semiringInst, ring.commSemiringInst, ring.commRingInst] do
          check inst
      for sr in (← getArithState).semirings do
        for inst in [sr.semiringInst, sr.commSemiringInst] do
          check inst
