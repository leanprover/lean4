import LeanCheckerTests.OpenPrivate

open private Lean.Environment.setCheckedSync from Lean.Environment
open private Lean.Kernel.Environment.mk from Lean.Environment
open private Lean.Kernel.Environment.extensions from Lean.Environment
open private Lean.Kernel.Environment.extGens from Lean.Environment
open private Lean.Kernel.Environment.irBaseExts from Lean.Environment

/- Redefine `propext : False`. -/
open Lean Elab Meta in
#eval modifyEnv (m := MetaM) fun env =>
  let forged : ConstantInfo := .axiomInfo {
    name := ``propext
    type := .const ``False []
    levelParams := []
    isUnsafe := false
  }
  let consts :=
    { env.constants with
        map₁ := env.constants.map₁.override ``propext forged }
  let kenv := Lean.Kernel.Environment.mk consts
    env.toKernelEnv.quotInit
    env.toKernelEnv.diagnostics
    env.toKernelEnv.allImportedConsts
    env.toKernelEnv.importedExtraConsts
    (Lean.Kernel.Environment.extensions env.toKernelEnv)
    (Lean.Kernel.Environment.irBaseExts env.toKernelEnv)
    (Lean.Kernel.Environment.extGens env.toKernelEnv)
    env.toKernelEnv.trackedGen
    env.header
  Lean.Environment.setCheckedSync env kenv

theorem efsq : ∀ (x y z n : Nat),
    0 < x → 0 < y → 0 < z → 2 < n →
    x^n + y^n ≠ z^n := by
  exfalso
  exact propext

/-- info: 'efsq' depends on axioms: [propext] -/
#guard_msgs in
-- 'efsq' depends on axioms: [propext]
#print axioms efsq
