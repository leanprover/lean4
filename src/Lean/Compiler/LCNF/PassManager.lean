/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Lean.Attributes
import Lean.Environment
import Lean.Meta.Basic

import Lean.Compiler.LCNF.CompilerM

namespace Lean.Compiler.LCNF

/--
The pipeline phase a certain `Pass` is supposed to happen in.
-/
inductive Phase where
  /-- Here we still carry most of the original type information, most
  of the dependent portion is already (partially) erased though. -/
  | base
  /-- In this phase polymorphism has been eliminated. -/
  | mono
  /-- In this phase impure stuff such as RC or efficient BaseIO transformations happen. -/
  | impure
deriving Inhabited

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
  The name of the `Pass`
  -/
  name : Name
  /--
  The actual pass function, operating on the `Decl`s.
  -/
  run : Array Decl → CompilerM (Array Decl)
  deriving Inhabited

/--
Can be used to install, remove, replace etc. passes by tagging a declaration
of type `PassInstaller` with the `cpass` attribute.
-/
structure PassInstaller where
  /--
  When the installer is run this function will receive a list of all
  current `Pass`es and return a new one, this can modify the list (and
  the `Pass`es contained within) in any way it wants.
  -/
  install : Array Pass → CompilerM (Array Pass)
  deriving Inhabited

/--
The `PassManager` used to store all `Pass`es that will be run within
pipeline.
-/
structure PassManager where
  passes : Array Pass
  deriving Inhabited

namespace Phase

def toNat : Phase → Nat
| .base => 0
| .mono => 1
| .impure => 2

instance : LT Phase where
  lt l r := l.toNat < r.toNat

instance : LE Phase where
  le l r := l.toNat ≤ r.toNat

instance {p1 p2 : Phase} : Decidable (p1 < p2) := Nat.decLt p1.toNat p2.toNat
instance {p1 p2 : Phase} : Decidable (p1 ≤ p2) := Nat.decLe p1.toNat p2.toNat

instance : ToString Phase where
  toString
    | .base => "base"
    | .mono => "mono"
    | .impure => "impure"

end Phase

namespace Pass

def mkPerDeclaration (name : Name) (run : Decl → CompilerM Decl) (phase : Phase) (occurrence : Nat := 0) : Pass where
  occurrence := occurrence
  phase := phase
  name := name
  run := fun xs => xs.mapM run

end Pass

namespace PassManager

def validate (manager : PassManager) : CompilerM Unit := do
  let mut current := .base
  for pass in manager.passes do
    if ¬(current ≤ pass.phase) then
      throwError s!"{pass.name} has phase {pass.phase} but should at least have {current}"
    current := pass.phase

def findHighestOccurrence (targetName : Name) (passes : Array Pass) : CompilerM Nat := do
  let mut highest := none
  for pass in passes do
      if pass.name == targetName then
        highest := some pass.occurrence
  let some val := highest | throwError s!"Could not find any occurrence of {targetName}"
  return val

end PassManager

namespace PassInstaller

def installAtEnd (p : Pass) : PassInstaller where
  install passes := return passes.push p

def append (passesNew : Array Pass) : PassInstaller where
  install passes := return passes ++ passesNew

def withEachOccurrence (targetName : Name) (f : Nat → PassInstaller) : PassInstaller where
  install passes := do
    let highestOccurrence ← PassManager.findHighestOccurrence targetName passes
    let mut passes := passes
    for occurrence in [0:highestOccurrence+1] do
      passes ← f occurrence |>.install passes
    return passes

def installAfter (targetName : Name) (p : Pass → Pass) (occurrence : Nat := 0) : PassInstaller where
  install passes :=
    if let some idx := passes.findIdx? (fun p => p.name == targetName && p.occurrence == occurrence) then
      let passUnderTest := passes[idx]!
      return passes.insertAt (idx + 1) (p passUnderTest)
    else
      throwError s!"Tried to insert pass after {targetName}, occurrence {occurrence} but {targetName} is not in the pass list"

def installAfterEach (targetName : Name) (p : Pass → Pass) : PassInstaller :=
    withEachOccurrence targetName (installAfter targetName p ·)

def installBefore (targetName : Name) (p : Pass → Pass) (occurrence : Nat := 0): PassInstaller where
  install passes :=
    if let some idx := passes.findIdx? (fun p => p.name == targetName && p.occurrence == occurrence) then
      let passUnderTest := passes[idx]!
      return passes.insertAt idx (p passUnderTest)
    else
      throwError s!"Tried to insert pass after {targetName}, occurrence {occurrence} but {targetName} is not in the pass list"

def installBeforeEachOccurrence (targetName : Name) (p : Pass → Pass) : PassInstaller :=
    withEachOccurrence targetName (installBefore targetName p ·)

def replacePass (targetName : Name) (p : Pass → Pass) (occurrence : Nat := 0) : PassInstaller where
  install passes := do
    let some idx := passes.findIdx? (fun p => p.name == targetName && p.occurrence == occurrence) | throwError s!"Tried to replace {targetName}, occurrence {occurrence} but {targetName} is not in the pass list"
    let target := passes[idx]!
    let replacement := p target
    return passes.set! idx replacement

def replaceEachOccurrence (targetName : Name) (p : Pass → Pass) : PassInstaller :=
    withEachOccurrence targetName (replacePass targetName p ·)

def run (manager : PassManager) (installer : PassInstaller) : CompilerM PassManager := do
  return { manager with passes := (←installer.install manager.passes) }

builtin_initialize passInstallerExt : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    name := `cpass,
    addImportedFn := fun imported => imported.foldl (init := #[]) fun acc a => acc.append a
    addEntryFn := fun is i => is.push i,
  }

def addPass (declName : Name) : CoreM Unit := do
  let info ← getConstInfo declName
  match info.type with
  | .const `Lean.Compiler.LCNF.PassInstaller .. =>
    modifyEnv fun env => passInstallerExt.addEntry env declName
  | _ =>
    throwError "invalid 'cpass' only 'PassInstaller's can be added via the 'cpass' attribute: {info.type}"

builtin_initialize
  registerBuiltinAttribute {
    name  := `cpass
    descr := "compiler passes for the code generator"
    add   := fun declName stx kind => do
      Attribute.Builtin.ensureNoArgs stx
      unless kind == AttributeKind.global do throwError "invalid attribute 'cpass', must be global"
      discard <| addPass declName
    applicationTime := .afterCompilation
  }

private unsafe def getPassInstallerUnsafe (declName : Name) : MetaM PassInstaller := do
  ofExcept <| (← getEnv).evalConstCheck PassInstaller (← getOptions) ``PassInstaller declName

@[implementedBy getPassInstallerUnsafe]
private opaque getPassInstaller (declName : Name) : MetaM PassInstaller

def runFromDecl (manager : PassManager) (declName : Name) : CompilerM PassManager := do
  let installer ← getPassInstaller declName |>.run'
  let newState ← installer.run manager
  newState.validate
  return newState

end PassInstaller

end Lean.Compiler.LCNF
