import SimpModuleIndex.Util
import SimpModuleIndex.B
import SimpModuleIndex.N

/-!
`B` adds `p_q` backward, which erases the forward theorem from `A`, so imported entries are replayed.
-/

open Lean Meta

example : SMI.f 0 = 1 := by simp
example : SMI.f 1 = 2 := by simp
example : SMI.m 1 = 3 := by simp
example (n : Nat) : SMI.q n = SMI.p n := by simp

#eval show MetaM Unit from do
  checkSimpSets [`SimpModuleIndex.A, `SimpModuleIndex.B, `SimpModuleIndex.M] (perModule := false)
  let d ← getSimpTheorems
  unless d.erased.contains (.decl ``SMI.p_q) do throwError "forward `p_q` not erased"
  unless (← d.post.getMatch (mkApp (mkConst ``SMI.f) (mkNatLit 0))).any (·.priority == 2000) do
    throwError "`f_zero` priority not replaced"

example : SMI.C.c Nat = 2 := rfl
example : SMI.C.c Int = 3 := rfl

#eval show MetaM Unit from do
  checkInstances [`SimpModuleIndex.A, `SimpModuleIndex.B, `SimpModuleIndex.M]
  unless (← isInstance ``SMI.instCInt) do throwError "`instCInt` is not an instance"
  unless (← getInstancePriority? ``SMI.instCNat2) == some 2000 do
    throwError "`instCNat2` priority not overridden"
