/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Compiler.LCNF.PullLetDecls
public import Lean.Compiler.LCNF.CSE
public import Lean.Compiler.LCNF.JoinPoints
public import Lean.Compiler.LCNF.Specialize
public import Lean.Compiler.LCNF.ToMono
public import Lean.Compiler.LCNF.LambdaLifting
public import Lean.Compiler.LCNF.FloatLetIn
public import Lean.Compiler.LCNF.ReduceArity
public import Lean.Compiler.LCNF.ElimDeadBranches
public import Lean.Compiler.LCNF.StructProjCases
public import Lean.Compiler.LCNF.ExtractClosed
public import Lean.Compiler.LCNF.Visibility
public import Lean.Compiler.LCNF.Simp

public section

namespace Lean.Compiler.LCNF

open PassInstaller

namespace Pass

def init : Pass where
  name  := `init
  run   := fun decls => do
    decls.forM (·.saveBase)
    return decls
  phase := .base
  shouldAlwaysRunCheck := true

def checkMeta : Pass where
  name  := `checkMeta
  run   := fun decls => do
    decls.forM LCNF.checkMeta
    return decls
  phase := .base

-- Helper pass used for debugging purposes
def trace (phase := Phase.base) : Pass where
  name  := `trace
  run   := pure
  phase := phase

def saveBase : Pass where
  occurrence := 0
  phase := .base
  name := `saveBase
  run decls := decls.mapM fun decl => do
    (← normalizeFVarIds decl).saveBase
    return decl
  shouldAlwaysRunCheck := true

def saveMono : Pass where
  occurrence := 0
  phase := .mono
  name := `saveMono
  run decls := decls.mapM fun decl => do
    (← normalizeFVarIds decl).saveMono
    return decl
  shouldAlwaysRunCheck := true

end Pass

open Pass

def builtinPassManager : PassManager := {
  basePasses := #[
    init,
    -- Check meta accesses now before optimizations may obscure references. This check should stay in
    -- `lean` if some compilation is moved out.
    Pass.checkMeta,
    pullInstances,
    cse (shouldElimFunDecls := false),
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
    -- Should be as early as possible but after `eagerLambdaLifting` to make sure instances are
    -- checked without nested functions whose bodies specialization does not require access to.
    checkTemplateVisibility,
    specialize,
    findJoinPoints (occurrence := 1),
    simp (occurrence := 2),
    cse (shouldElimFunDecls := false) (occurrence := 1),
    saveBase, -- End of base phase
    -- should come last so it can see all created decls
    -- pass must be run for each phase; see `base/monoTransparentDeclsExt`
    inferVisibility (phase := .base),
    toMono,
  ]
  monoPasses := #[
    simp (occurrence := 3) (phase := .mono),
    reduceJpArity (phase := .mono),
    structProjCases,
    extendJoinPointContext (phase := .mono) (occurrence := 0),
    floatLetIn (phase := .mono) (occurrence := 1),
    reduceArity,
    commonJoinPointArgs,
    simp (occurrence := 4) (phase := .mono),
    floatLetIn (phase := .mono) (occurrence := 2),
    lambdaLifting,
  ]
  monoPassesNoLambda := #[
    extendJoinPointContext (phase := .mono) (occurrence := 1),
    simp (occurrence := 5) (phase := .mono),
    elimDeadBranches,
    cse (occurrence := 2) (phase := .mono),
    saveMono,  -- End of mono phase
    inferVisibility (phase := .mono),
    extractClosed,
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
    throwAttrDeclNotOfExpectedType `cpass declName info.type (mkConst ``PassInstaller)

builtin_initialize
  registerBuiltinAttribute {
    name  := `cpass
    descr := "compiler passes for the code generator"
    add   := fun declName stx kind => do
      Attribute.Builtin.ensureNoArgs stx
      unless kind == AttributeKind.global do throwAttrMustBeGlobal `cpass kind
      ensureAttrDeclIsMeta `cpass declName kind
      discard <| addPass declName
    applicationTime := .afterCompilation
  }

builtin_initialize
  registerTraceClass `Compiler.saveBase (inherited := true)
  registerTraceClass `Compiler.saveMono (inherited := true)
  registerTraceClass `Compiler.trace (inherited := true)

end Lean.Compiler.LCNF
