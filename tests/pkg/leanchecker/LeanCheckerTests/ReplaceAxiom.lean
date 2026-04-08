import LeanCheckerTests.OpenPrivate

open private Lean.Environment.setCheckedSync from Lean.Environment
open private Lean.Kernel.Environment.mk from Lean.Environment
open private Lean.Kernel.Environment.extensions from Lean.Environment

/- Redefine `propext : False`. -/
open Lean Elab Meta in
#eval modifyEnv (m := MetaM) fun env =>
  let consts :=
    { env.constants with
        map₁ := env.constants.map₁.insert ``propext (.axiomInfo {
          name := ``propext
          type := .const ``False []
          levelParams := []
          isUnsafe := false
        })
    }
  let kenv := Lean.Kernel.Environment.mk consts
    env.toKernelEnv.quotInit
    env.toKernelEnv.diagnostics
    env.toKernelEnv.const2ModIdx
    (Lean.Kernel.Environment.extensions env.toKernelEnv)
    {}
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
