/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Lean.Compiler.LCNF.PassManager
import Lean.Compiler.LCNF.PullLetDecls
import Lean.Compiler.LCNF.CSE
import Lean.Compiler.LCNF.Simp
import Lean.Compiler.LCNF.PullFunDecls
import Lean.Compiler.LCNF.ReduceJpArity
import Lean.Compiler.LCNF.JoinPoints
import Lean.Compiler.LCNF.Specialize
import Lean.Compiler.LCNF.PhaseExt

namespace Lean.Compiler.LCNF

open PassInstaller

def init : Pass where
  name  := `init
  run   := fun decls => do
    decls.forM (·.saveBase)
    return decls
  phase := .base

def builtinPassManager : PassManager := {
  passes := #[
    init,
    pullInstances,
    cse,
    simp,
    findJoinPoints,
    pullFunDecls,
    reduceJpArity,
    simp { etaPoly := true, inlinePartial := true, implementedBy := true } (occurrence := 1),
    specialize,
    simp (occurrence := 2),
    cse,
    saveBase -- End of base phase
  ]
}

def runImportedDecls (importedDeclNames : Array (Array Name)) : CoreM PassManager := do
  let mut m := builtinPassManager
  for declNames in importedDeclNames do
    for declName in declNames do
      m ← runFromDecl m declName
  return m

builtin_initialize passManagerExt : PersistentEnvExtension Name (Name × PassManager) (List Name × PassManager) ←
  registerPersistentEnvExtension {
    name := `cpass
    mkInitial := return ([], builtinPassManager)
    addImportedFn := fun ns => return ([], ← ImportM.runCoreM <| runImportedDecls ns)
    addEntryFn := fun (installerDeclNames, _) (installerDeclName, managerNew) => (installerDeclName :: installerDeclNames, managerNew)
    exportEntriesFn := fun s => s.1.reverse.toArray
  }

def getPassManager : CoreM PassManager :=
  return passManagerExt.getState (← getEnv) |>.2

def addPass (declName : Name) : CoreM Unit := do
  let info ← getConstInfo declName
  match info.type with
  | .const `Lean.Compiler.LCNF.PassInstaller .. =>
    let managerNew ← runFromDecl (← getPassManager) declName
    modifyEnv fun env => passManagerExt.addEntry env (declName, managerNew)
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

builtin_initialize
  registerTraceClass `Compiler.saveBase (inherited := true)

end Lean.Compiler.LCNF
