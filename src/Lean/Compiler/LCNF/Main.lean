/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Compiler.Options
public import Lean.Compiler.IR
public import Lean.Compiler.LCNF.Passes
public import Lean.Compiler.LCNF.ToDecl
public import Lean.Compiler.LCNF.Check
import Lean.Meta.Match.MatcherInfo
import Lean.Compiler.LCNF.SplitSCC
public section
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
  let env ← getEnv
  if isExtern env declName then return true
  -- Look up the decl in the kernel environment, since it will appear there
  -- as an axiom (rather than a definition) in the case of a kernel error.
  let some info := env.constants.find? declName | return false
  unless info.hasValue (allowOpaque := true) do return false
  if hasMacroInlineAttribute env declName then return false
  if (getImplementedBy? env declName).isSome then return false
  if (← Meta.isMatcher declName) then return false
  if isCasesOnLike env declName then return false
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
def checkpoint (stepName : Name) (decls : Array Decl) (shouldCheck : Bool) : CompilerM Unit := do
  for decl in decls do
    trace[Compiler.stat] "{decl.name} : {decl.size}"
    withOptions (fun opts => opts.set `pp.motives.pi false) do
      let clsName := `Compiler ++ stepName
      if (← Lean.isTracingEnabledFor clsName) then
        Lean.addTrace clsName m!"size: {decl.size}\n{← ppDecl' decl}"
      if shouldCheck then
        decl.check

def isValidMainType (type : Expr) : Bool :=
  let isValidResultName (name : Name) : Bool :=
    name == ``UInt32 || name == ``Unit || name == ``PUnit
  match type with
  | .forallE _ d b _ =>
    match d, b with
    | .app (.const ``List _) (.const ``String _), .app (.const ``IO _) (.const resultName _) =>
      isValidResultName resultName
    | _, _ => false
  | .app (.const ``IO _) (.const resultName _) =>
    isValidResultName resultName
  | _ => false

namespace PassManager

def run (declNames : Array Name) : CompilerM (Array (Array IR.Decl)) := withAtLeastMaxRecDepth 8192 do
  /-
  Note: we need to increase the recursion depth because we currently do to save phase1
  declarations in .olean files. Then, we have to recursively compile all dependencies,
  and it often creates a very deep recursion.
  Moreover, some declarations get very big during simplification.
  -/
  for declName in declNames do
    if let some fnName := Compiler.getImplementedBy? (← getEnv) declName then
      if !isDeclPublic (← getEnv) fnName then
        if let some decl ← getLocalDeclAt? fnName .base then
          trace[Compiler.inferVisibility] m!"Marking {fnName} as opaque because it implements {declName}"
          LCNF.markDeclPublicRec .base decl
          if let some decl ← getLocalDeclAt? fnName .mono then
            LCNF.markDeclPublicRec .mono decl
  let declNames ← declNames.filterM (shouldGenerateCode ·)
  if declNames.isEmpty then return #[]
  for declName in declNames do
    if declName == `main then
      if let some info ← getDeclInfo? declName then
        if !(isValidMainType info.type) then
          throwError "`main` function must have type `(List String →)? IO (UInt32 | Unit | PUnit)`"
  let decls ← declNames.mapM toDecl
  let decls := markRecDecls decls
  let manager ← getPassManager
  let isCheckEnabled := compiler.check.get (← getOptions)
  let decls ← runPassManagerPart "compilation (LCNF base)" manager.basePasses decls isCheckEnabled
  let decls ← runPassManagerPart "compilation (LCNF mono)" manager.monoPasses decls isCheckEnabled
  let sccs ← withTraceNode `Compiler.splitSCC (fun _ => return m!"Splitting up SCC") do
    splitScc decls
  sccs.mapM fun decls => do
    let decls ← runPassManagerPart "compilation (LCNF mono)" manager.monoPassesNoLambda decls isCheckEnabled
    if (← Lean.isTracingEnabledFor `Compiler.result) then
      for decl in decls do
        let decl ← normalizeFVarIds decl
        Lean.addTrace `Compiler.result m!"size: {decl.size}\n{← ppDecl' decl}"
    profileitM Exception "compilation (IR)" (← getOptions) do
      let irDecls ← IR.toIR decls
      IR.compile irDecls
where
  runPassManagerPart (profilerName : String) (passes : Array Pass) (decls : Array Decl)
      (isCheckEnabled : Bool) : CompilerM (Array Decl) := do
    profileitM Exception profilerName (← getOptions) do
      let mut decls := decls
      for pass in passes do
        decls ← withTraceNode `Compiler (fun _ => return m!"compiler phase: {pass.phase}, pass: {pass.name}") do
          withPhase pass.phase <| pass.run decls
        withPhase pass.phaseOut <| checkpoint pass.name decls (isCheckEnabled || pass.shouldAlwaysRunCheck)
      return decls

end PassManager

def compile (declNames : Array Name) : CoreM (Array (Array IR.Decl)) :=
  CompilerM.run <| PassManager.run declNames

def showDecl (phase : Phase) (declName : Name) : CoreM Format := do
  let some decl ← getDeclAt? declName phase | return "<not-available>"
  ppDecl' decl

def main (declNames : Array Name) : CoreM Unit := do
  withTraceNode `Compiler (fun _ => return m!"compiling: {declNames}") do
    CompilerM.run <| discard <| PassManager.run declNames

builtin_initialize
  compileDeclsRef.set main

builtin_initialize
  registerTraceClass `Compiler.init (inherited := true)
  registerTraceClass `Compiler.test (inherited := true)
  registerTraceClass `Compiler.result (inherited := true)
  registerTraceClass `Compiler.jp

end Lean.Compiler.LCNF
