import LeanCheckerTests.OpenPrivate

open private Lean.Environment.setCheckedSync from Lean.Environment
open private Lean.Kernel.Environment.mk from Lean.Environment
open private Lean.Kernel.Environment.extensions from Lean.Environment

open Lean in
/-- Overwrites the entry for `n` in the imported constants view, for test purposes. -/
partial def overrideImported (t : ImportedConsts ConstantInfo) (n : Name) (c : ConstantInfo) :
    ImportedConsts ConstantInfo :=
  modAt t n setter
where
  setter : ImportedConsts ConstantInfo → ImportedConsts ConstantInfo
    | .merged k _ cs hs => .merged k (some (c, 0)) cs hs
    | .mod i (.node k _ cs hs) => .merged k (some (c, 0)) (cs.map (.mod i)) hs
  modAt (t : ImportedConsts ConstantInfo) (n : Name)
      (f : ImportedConsts ConstantInfo → ImportedConsts ConstantInfo) :
      ImportedConsts ConstantInfo :=
    match n with
    | .anonymous => f t
    | n => modAt t n.getPrefix (step n f)
  step (n : Name) (f : ImportedConsts ConstantInfo → ImportedConsts ConstantInfo) :
      ImportedConsts ConstantInfo → ImportedConsts ConstantInfo
    | .merged k e cs hs => (.merged k e · hs) <| cs.map fun c =>
        if keyOf c == n then f c else c
    | .mod i (.node k v cs hs) => (.merged k (v.map ((·, i))) · hs) <| cs.map fun c =>
        if (match c with | .node ck .. => ck) == n then f (.mod i c) else .mod i c
  keyOf : ImportedConsts ConstantInfo → Name
    | .mod _ (.node k ..) => k
    | .merged k .. => k

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
