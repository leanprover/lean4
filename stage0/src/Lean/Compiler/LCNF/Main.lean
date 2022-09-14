/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.Options
import Lean.Compiler.LCNF.PassManager
import Lean.Compiler.LCNF.Passes
import Lean.Compiler.LCNF.PrettyPrinter
import Lean.Compiler.LCNF.ToDecl
import Lean.Compiler.LCNF.Check
import Lean.Compiler.LCNF.Stage1
import Lean.Compiler.LCNF.PullLetDecls
import Lean.Compiler.LCNF.CSE

namespace Lean.Compiler.LCNF
/--
We do not generate code for `declName` if
- Its type is a proposition.
- Its type is a type former.
- It is tagged as `[macroInline]`.
- It is a type class instance.

Remark: we still generate code for declarations tagged as `[inline]`
and `[specialize]` since they can be partially applied.
-/
def shouldGenerateCode (declName : Name) : CoreM Bool := do
  if (← isCompIrrelevant |>.run') then return false
  let env ← getEnv
  if hasMacroInlineAttribute env declName then return false
  if (← Meta.isMatcher declName) then return false
  if isCasesOnRecursor env declName then return false
  -- TODO: check if type class instance
  return true
where
  isCompIrrelevant : MetaM Bool := do
    let info ← getConstInfo declName
    Meta.isProp info.type <||> Meta.isTypeFormerType info.type

/--
A checkpoint in code generation to print all declarations in between
compiler passes in order to ease debugging.
The trace can be viewed with `set_option trace.Compiler.step true`.
-/
def checkpoint (stepName : Name) (decls : Array Decl) : CompilerM Unit := do
  for decl in decls do
    trace[Compiler.stat] "{decl.name} : {decl.size}"
    withOptions (fun opts => opts.setBool `pp.motives.pi false) do
      let clsName := `Compiler ++ stepName
      if (← Lean.isTracingEnabledFor clsName) then
        Lean.addTrace clsName m!"size: {decl.size}\n{← ppDecl decl}"
      if compiler.check.get (← getOptions) then
        decl.check
  if compiler.check.get (← getOptions) then
    checkDeadLocalDecls decls

namespace PassManager

def run (declNames : Array Name) : CompilerM (Array Decl) := do
  let declNames ← declNames.filterM (shouldGenerateCode ·)
  if declNames.isEmpty then return #[]
  let mut decls ← declNames.mapM toDecl
  let mut manager := { passes := #[{ name := `init, run := pure, phase := .base }] }
  let installers := PassInstaller.passInstallerExt.getState (←getEnv)
  manager ← installers.foldlM (init := manager) PassInstaller.runFromDecl
  for pass in manager.passes do
    trace[Compiler] s!"Running pass: {pass.name}"
    decls ← pass.run decls
    checkpoint pass.name decls
  saveStage1Decls decls
  if (← Lean.isTracingEnabledFor `Compiler.result) then
    for decl in decls do
      Lean.addTrace `Compiler.result m!"size: {decl.size}\n{← ppDecl decl}"
  return decls

end PassManager

@[export lean_compile_stage1]
def compileStage1Impl (declNames : Array Name) : CoreM (Array Decl) :=
  CompilerM.run do
    PassManager.run declNames

builtin_initialize
  registerTraceClass `Compiler.init (inherited := true)
  registerTraceClass `Compiler.test (inherited := true)
  registerTraceClass `Compiler.result (inherited := true)
  registerTraceClass `Compiler.jp

end Lean.Compiler.LCNF
