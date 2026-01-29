/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Compiler.LCNF.CompilerM

public section

namespace Lean.Compiler.LCNF

@[expose] def Phase.toNat : Phase → Nat
  | .base => 0
  | .mono => 1

instance : LT Phase where
  lt l r := l.toNat < r.toNat

instance : LE Phase where
  le l r := l.toNat ≤ r.toNat

instance {p1 p2 : Phase} : Decidable (p1 < p2) := Nat.decLt p1.toNat p2.toNat
instance {p1 p2 : Phase} : Decidable (p1 ≤ p2) := Nat.decLe p1.toNat p2.toNat

@[simp] theorem Phase.le_refl (p : Phase) : p ≤ p := by
  cases p <;> decide

/--
A single compiler `Pass`, consisting of the actual pass function operating
on the `Decl`s as well as meta information.
-/
structure Pass where
  /--
  Which occurrence of the pass in the pipeline this is.
  Some passes, like simp, can occur multiple times in the pipeline.
  For most passes this value does not matter.
  -/
  occurrence : Nat := 0
  /--
  Which phase this `Pass` is supposed to run in
  -/
  phase : Phase
  /--
  Resulting phase.
  -/
  phaseOut : Phase := phase
  phaseInv : phaseOut ≥ phase := by simp +arith +decide
  /--
  Whether IR validation checks should always run after this pass, regardless
  of configuration options.
  -/
  shouldAlwaysRunCheck : Bool := false
  /--
  The name of the `Pass`
  -/
  name : Name
  /--
  The actual pass function, operating on the `Decl`s.
  -/
  run : Array Decl → CompilerM (Array Decl)

instance : Inhabited Pass where
  default := { phase := .base, name := default, run := fun decls => return decls }

/--
Can be used to install, remove, replace etc. passes by tagging a declaration
of type `PassInstaller` with the `cpass` attribute.
-/
structure PassInstaller where
  /-- Affected phase. -/
  phase : Phase
  /--
  When the installer is run this function will receive a list of all
  current `Pass`es and return a new one, this can modify the list (and
  the `Pass`es contained within) in any way it wants.
  -/
  install : Array Pass → CoreM (Array Pass)
  deriving Inhabited

/--
The `PassManager` used to store all `Pass`es that will be run within
pipeline.
-/
structure PassManager where
  basePasses : Array Pass
  monoPasses : Array Pass
  monoPassesNoLambda : Array Pass
  deriving Inhabited

instance : ToString Phase where
  toString
    | .base => "base"
    | .mono => "mono"

namespace Pass

def mkPerDeclaration (name : Name) (run : Decl → CompilerM Decl) (phase : Phase) (occurrence : Nat := 0) : Pass where
  occurrence := occurrence
  phase := phase
  name := name
  run := fun xs => xs.mapM run

end Pass

namespace PassManager

private def validatePasses (phase : Phase) (passes : Array Pass) : CoreM Unit := do
  for pass in passes do
    if pass.phase != phase then
      throwError s!"{pass.name} has phase {pass.phase} but should have {phase}"

def validate (manager : PassManager) : CoreM Unit := do
  validatePasses .base manager.basePasses
  validatePasses .mono manager.monoPasses
  validatePasses .mono manager.monoPassesNoLambda

def findOccurrenceBounds (targetName : Name) (passes : Array Pass) : CoreM (Nat × Nat) := do
  let mut lowest := none
  let mut highest := none
  for pass in passes do
      if pass.name == targetName then
        lowest := if lowest.isNone then some pass.occurrence else lowest
        highest := some pass.occurrence
  let ⟨some lowestVal, some highestVal⟩ := Prod.mk lowest highest | throwError s!"Could not find any occurrence of {targetName}"
  return ⟨lowestVal, highestVal⟩

end PassManager

namespace PassInstaller

def installAtEnd (phase : Phase) (p : Pass) : PassInstaller where
  phase
  install passes := return passes.push p

def append (phase : Phase) (passesNew : Array Pass) : PassInstaller where
  phase
  install passes := return passes ++ passesNew

def withEachOccurrence (phase : Phase) (targetName : Name) (f : Nat → PassInstaller) : PassInstaller where
  phase
  install passes := do
    let ⟨lowestOccurrence, highestOccurrence⟩ ← PassManager.findOccurrenceBounds targetName passes
    let mut passes := passes
    for occurrence in lowestOccurrence...=highestOccurrence do
      let installer := f occurrence
      if installer.phase != phase then
        panic! "phase mismatch"
      passes ← installer.install passes
    return passes

def installAfter (phase : Phase) (targetName : Name) (p : Pass → Pass) (occurrence : Nat := 0) : PassInstaller where
  phase
  install passes :=
    if let some idx := passes.findFinIdx? (fun p => p.name == targetName && p.occurrence == occurrence) then
      let passUnderTest := passes[idx]
      return passes.insertIdx (idx + 1) (p passUnderTest)
    else
      throwError s!"Tried to insert pass after {targetName}, occurrence {occurrence} but {targetName} is not in the pass list"

def installAfterEach (phase : Phase) (targetName : Name) (p : Pass → Pass) : PassInstaller :=
    withEachOccurrence phase targetName (installAfter phase targetName p ·)

def installBefore (phase : Phase) (targetName : Name) (p : Pass → Pass) (occurrence : Nat := 0): PassInstaller where
  phase
  install passes :=
    if let some idx := passes.findFinIdx? (fun p => p.name == targetName && p.occurrence == occurrence) then
      let passUnderTest := passes[idx]
      return passes.insertIdx idx (p passUnderTest)
    else
      throwError s!"Tried to insert pass after {targetName}, occurrence {occurrence} but {targetName} is not in the pass list"

def installBeforeEachOccurrence (phase : Phase) (targetName : Name) (p : Pass → Pass) : PassInstaller :=
    withEachOccurrence phase targetName (installBefore phase targetName p ·)

def replacePass (phase : Phase) (targetName : Name) (p : Pass → Pass) (occurrence : Nat := 0) : PassInstaller where
  phase
  install passes := do
    let some idx := passes.findIdx? (fun p => p.name == targetName && p.occurrence == occurrence) | throwError s!"Tried to replace {targetName}, occurrence {occurrence} but {targetName} is not in the pass list"
    return passes.modify idx p

def replaceEachOccurrence (phase : Phase) (targetName : Name) (p : Pass → Pass) : PassInstaller :=
    withEachOccurrence phase targetName (replacePass phase targetName p ·)

def run (manager : PassManager) (installer : PassInstaller) : CoreM PassManager := do
  match installer.phase with
  | .base =>
    return { manager with basePasses := (← installer.install manager.basePasses) }
  | .mono =>
    return { manager with monoPasses := (← installer.install manager.monoPasses) }

private unsafe def getPassInstallerUnsafe (declName : Name) : CoreM PassInstaller := do
  ofExcept <| (← getEnv).evalConstCheck PassInstaller (← getOptions) ``PassInstaller declName

@[implemented_by getPassInstallerUnsafe]
private opaque getPassInstaller (declName : Name) : CoreM PassInstaller

def runFromDecl (manager : PassManager) (declName : Name) : CoreM PassManager := do
  let installer ← getPassInstaller declName
  let newState ← PassInstaller.run manager installer
  newState.validate
  return newState

end PassInstaller

end Lean.Compiler.LCNF
