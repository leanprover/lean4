import Std.Tactic.BVDecide

/-!
Tests for `Std.Tactic.BVDecide.LRAT.KernelVM.lratVMProg`, an LRAT checker for the kernel VM.
-/

open Std.Tactic.BVDecide Std.Tactic.BVDecide.LRAT.KernelVM Lean.KernelVM

/-- `x ∨ y`, `¬x ∨ y`, `x ∨ ¬y`, `¬x ∨ ¬y` -/
def cnf : Std.Sat.CNF Nat := .mk #[
  .ofLiterals [(0, true), (1, true)], .ofLiterals [(0, false), (1, true)],
  .ofLiterals [(0, true), (1, false)], .ofLiterals [(0, false), (1, false)]]

/-- Derives `y` from clauses 1 and 2, then the empty clause from 3, 4 and `y`. -/
def proof : Array LRAT.IntAction := #[.addRup 5 #[2] #[1, 2], .del #[1, 2], .addEmpty 6 #[5, 3, 4]]

def cnfNat := encodeCNF cnf (maxActionId proof)
def proofNat := (encodeProof proof).get!

example : run lratVMProg [cnfNat, proofNat] lratVMFuel = true := by decide +kernel

-- A hint that is neither unit nor conflicting fails.
example : run lratVMProg [cnfNat, (encodeProof #[.addRup 5 #[2] #[1, 3]]).get!] lratVMFuel = false := by
  decide +kernel

-- A proof that does not derive the empty clause fails.
example : run lratVMProg [cnfNat, (encodeProof #[.addRup 5 #[2] #[1, 2]]).get!] lratVMFuel = false := by
  decide +kernel
