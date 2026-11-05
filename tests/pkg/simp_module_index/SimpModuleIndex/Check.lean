import SimpModuleIndex.Util
import SimpModuleIndex.A
import SimpModuleIndex.N

/-!
Without constants that are simp theorems in both directions, imported lemma names are looked up in
the per-module arrays.
-/

open Lean Meta

example : SMI.f 0 = 1 := by simp
example : SMI.f (SMI.f 3) = 5 := by simp
example : SMI.f 2 = 3 := by
  fail_if_success simp
  rfl
open SMI.Sc in
example : SMI.f 2 = 3 := by simp
-- `M` is imported at the private level here
example : SMI.m 1 = 3 := by simp
example (n : Nat) : SMI.p n = SMI.q n := by simp

#eval show MetaM Unit from
  checkSimpSets [`SimpModuleIndex.A, `SimpModuleIndex.M] (perModule := true)

example : SMI.C.c Nat = 1 := rfl
example : SMI.C Int := by
  fail_if_success exact inferInstance
  exact ⟨0⟩
example : SMI.C String := by
  fail_if_success exact inferInstance
  exact ⟨0⟩
open SMI.Sc in
example : SMI.C.c String = 4 := rfl
-- `M` is imported at the private level here
example : SMI.D.d Bool = 6 := rfl

#eval show MetaM Unit from do
  checkInstances [`SimpModuleIndex.A, `SimpModuleIndex.M]
  unless (← isInstance ``SMI.instCNat2) && !(← isInstance ``SMI.instCInt) do
    throwError "unexpected instance names"
  unless (← getInstancePriority? ``SMI.instCNat2) == some (eval_prio low) do
    throwError "unexpected priority"

-- changes on top of the imported lemma names
attribute [-simp] SMI.f_zero
example : SMI.f 0 = 1 := by
  fail_if_success simp
  rfl
-- `simp [thm]` undoes `-simp` (unlike `attribute [simp]`, see #5852)
example : SMI.f 0 = 1 := by simp [SMI.f_zero]
example : SMI.f 0 = 1 := by simp [SMI.f]

#eval show MetaM Unit from do
  let d ← getSimpTheorems
  unless !d.lemmaNames.contains (.decl ``SMI.f_zero) && d.lemmaNames.contains (.decl ``SMI.f_f) &&
      !d.lemmaNames.contains (.decl ``SMI.f_two) && !d.lemmaNames.contains (.decl ``SMI.f_f (inv := true)) do
    throwError "unexpected lemma names"
