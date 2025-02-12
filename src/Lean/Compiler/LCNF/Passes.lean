/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Compiler.LCNF.PassManager
import Lean.Compiler.LCNF.PullLetDecls
import Lean.Compiler.LCNF.CSE
import Lean.Compiler.LCNF.Simp
import Lean.Compiler.LCNF.PullFunDecls
import Lean.Compiler.LCNF.ReduceJpArity
import Lean.Compiler.LCNF.JoinPoints
import Lean.Compiler.LCNF.Specialize
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.LCNF.ToMono
import Lean.Compiler.LCNF.LambdaLifting
import Lean.Compiler.LCNF.FloatLetIn
import Lean.Compiler.LCNF.ReduceArity
import Lean.Compiler.LCNF.ElimDeadBranches

namespace Lean.Compiler.LCNF

open PassInstaller

def init : Pass where
  name  := `init
  run   := fun decls => do
    decls.forM (·.saveBase)
    return decls
  phase := .base

-- Helper pass used for debugging purposes
def trace (phase := Phase.base) : Pass where
  name  := `trace
  run   := pure
  phase := phase

def saveBase : Pass :=
  .mkPerDeclaration `saveBase (fun decl => do (← normalizeFVarIds decl).saveBase; return decl) .base

def saveMono : Pass :=
  .mkPerDeclaration `saveMono (fun decl => do (← normalizeFVarIds decl).saveMono; return decl) .mono

def builtinPassManager : PassManager := {
  passes := #[
    init,
    pullInstances,
    cse,
    simp,
    floatLetIn,
    findJoinPoints,
    pullFunDecls,
    reduceJpArity,
    /-
    We apply `implementedBy` replacements before `specialize` to ensure we specialize the replacement.
    One possible improvement is to perform only the replacements if the target declaration is a specialization target,
    and on phase 2 (aka mono) perform the remaining replacements.
    -/
    simp { etaPoly := true, inlinePartial := true, implementedBy := true } (occurrence := 1),
    eagerLambdaLifting,
    specialize,
    simp (occurrence := 2),
    cse (occurrence := 1),
    saveBase, -- End of base phase
    toMono,
    simp (occurrence := 3) (phase := .mono),
    reduceJpArity (phase := .mono),
    extendJoinPointContext (phase := .mono) (occurrence := 0),
    floatLetIn (phase := .mono) (occurrence := 1),
    reduceArity,
    commonJoinPointArgs,
    simp (occurrence := 4) (phase := .mono),
    floatLetIn (phase := .mono) (occurrence := 2),
    elimDeadBranches,
    lambdaLifting,
    extendJoinPointContext (phase := .mono) (occurrence := 1),
    simp (occurrence := 5) (phase := .mono),
    cse (occurrence := 2) (phase := .mono),
    saveMono  -- End of mono phase
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
    mkInitial := return ([], builtinPassManager)
    addImportedFn := fun ns => return ([], ← ImportM.runCoreM <| runImportedDecls ns)
    addEntryFn := fun (installerDeclNames, _) (installerDeclName, managerNew) => (installerDeclName :: installerDeclNames, managerNew)
    exportEntriesFn := fun s => s.1.reverse.toArray
    asyncMode := .sync
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
  registerTraceClass `Compiler.saveMono (inherited := true)
  registerTraceClass `Compiler.trace (inherited := true)

end Lean.Compiler.LCNF
