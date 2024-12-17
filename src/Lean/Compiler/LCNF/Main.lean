/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Compiler.Options
import Lean.Compiler.ExternAttr
import Lean.Compiler.LCNF.PassManager
import Lean.Compiler.LCNF.Passes
import Lean.Compiler.LCNF.PrettyPrinter
import Lean.Compiler.LCNF.ToDecl
import Lean.Compiler.LCNF.Check
import Lean.Compiler.LCNF.PullLetDecls
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.LCNF.CSE

namespace Lean.Compiler.LCNF
/--
We do not generate code for `declName` if
- Its type is a proposition.
- Its type is a type former.
- It is tagged as `[macro_inline]`.
- It is a type class instance.

Remark: we still generate code for declarations tagged as `[inline]`
and `[specialize]` since they can be partially applied.
-/
def shouldGenerateCode (declName : Name) : CoreM Bool := do
  if (← isCompIrrelevant |>.run') then return false
  let some info ← getDeclInfo? declName | return false
  unless info.hasValue (allowOpaque := true) do return false
  let env ← getEnv
  if isExtern env declName then return false
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
        Lean.addTrace clsName m!"size: {decl.size}\n{← ppDecl' decl}"
      if compiler.check.get (← getOptions) then
        decl.check
  if compiler.check.get (← getOptions) then
    checkDeadLocalDecls decls

namespace PassManager

def run (declNames : Array Name) : CompilerM (Array Decl) := withAtLeastMaxRecDepth 8192 do
  /-
  Note: we need to increase the recursion depth because we currently do to save phase1
  declarations in .olean files. Then, we have to recursively compile all dependencies,
  and it often creates a very deep recursion.
  Moreover, some declarations get very big during simplification.
  -/
  let declNames ← declNames.filterM (shouldGenerateCode ·)
  if declNames.isEmpty then return #[]
  let mut decls ← declNames.mapM toDecl
  decls := markRecDecls decls
  let manager ← getPassManager
  for pass in manager.passes do
    decls ← withTraceNode `Compiler (fun _ => return m!"new compiler phase: {pass.phase}, pass: {pass.name}") do
      withPhase pass.phase <| pass.run decls
    withPhase pass.phaseOut <| checkpoint pass.name decls
  if (← Lean.isTracingEnabledFor `Compiler.result) then
    for decl in decls do
      -- We display the declaration saved in the environment because the names have been normalized
      let some decl' ← getDeclAt? decl.name .mono | unreachable!
      Lean.addTrace `Compiler.result m!"size: {decl.size}\n{← ppDecl' decl'}"
  return decls

end PassManager

def compile (declNames : Array Name) : CoreM (Array Decl) :=
  CompilerM.run <| PassManager.run declNames

def showDecl (phase : Phase) (declName : Name) : CoreM Format := do
  let some decl ← getDeclAt? declName phase | return "<not-available>"
  ppDecl' decl

@[export lean_lcnf_compile_decls]
def main (declNames : List Name) : CoreM Unit := do
  profileitM Exception "compilation new" (← getOptions) do
    withTraceNode `Compiler (fun _ => return m!"compiling new: {declNames}") do
      CompilerM.run <| discard <| PassManager.run declNames.toArray

builtin_initialize
  registerTraceClass `Compiler.init (inherited := true)
  registerTraceClass `Compiler.test (inherited := true)
  registerTraceClass `Compiler.result (inherited := true)
  registerTraceClass `Compiler.jp

end Lean.Compiler.LCNF
