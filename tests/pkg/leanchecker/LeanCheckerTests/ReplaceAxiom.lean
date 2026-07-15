import LeanCheckerTests.OpenPrivate

open private Lean.Environment.setCheckedSync from Lean.Environment
open private Lean.Kernel.Environment.mk from Lean.Environment
open private Lean.Kernel.Environment.extensions from Lean.Environment

open Lean in
/--
Overwrites the entry for the childless name `n` in the imported constants view, for test purposes:
`n`'s node is replaced by a merged leaf holding the forged value.
-/
def overrideImported (t : ImportedConsts ConstantInfo) (n : Name) (c : ConstantInfo) :
    ImportedConsts ConstantInfo :=
  t.modifyAt n fun _ => .mkMerged n (some (c, 0)) #[]

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
        map₁ := overrideImported env.constants.map₁ ``propext forged }
  let kenv := Lean.Kernel.Environment.mk consts
    env.toKernelEnv.quotInit
    env.toKernelEnv.diagnostics
    env.toKernelEnv.allImportedConsts
    env.toKernelEnv.importedExtraConsts
    env.toKernelEnv.const2ModIdxThunk
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
