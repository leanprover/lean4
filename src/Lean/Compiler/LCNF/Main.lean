/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
import Lean.Compiler.Options
import Lean.Compiler.IR
import Lean.Compiler.LCNF.Passes
import Lean.Compiler.LCNF.ToDecl
import Lean.Compiler.LCNF.Check
import Lean.Meta.Match.MatcherInfo
import Lean.Compiler.LCNF.SplitSCC
public import Lean.Compiler.IR.Basic
public import Lean.Compiler.LCNF.CompilerM

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
def checkpoint (stepName : Name) (decls : Array (Decl pu)) (shouldCheck : Bool) : CompilerM Unit := do
  for decl in decls do
    trace[Compiler.stat] "{decl.name} : {decl.size}"
    withOptions (fun opts => opts.set `pp.motives.pi false) do
      let clsName := `Compiler ++ stepName
      if (← Lean.isTracingEnabledFor clsName) then
        Lean.addTrace clsName m!"size: {decl.size}\n{← ppDecl' decl (← getPhase)}"
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
            if let some decl ← getLocalDeclAt? fnName .impure then
              LCNF.markDeclPublicRec .impure decl
  let declNames ← declNames.filterM (shouldGenerateCode ·)
  if declNames.isEmpty then return #[]
  for declName in declNames do
    if declName == `main then
      if let some info ← getDeclInfo? declName then
        if !(isValidMainType info.type) then
          throwError "`main` function must have type `(List String →)? IO (UInt32 | Unit | PUnit)`"
  let decls ← declNames.mapM toDecl

  for decl in decls do
    decl.value.forCodeM fun code => code.forM fun
      | .let decl .. => do
        if let .const c .. := decl.value then
          let c := Compiler.getImplementedBy? (← getEnv) c |>.getD c
          let c := if (← hasConst (mkUnsafeRecName c)) then mkUnsafeRecName c else c
          if postponedCompileDeclsExt.getState (← getEnv) |>.contains c then
            match (← getConstInfo c) with
            | .defnInfo info =>
              modifyEnv (postponedCompileDeclsExt.modifyState · fun s => info.all.foldl (·.erase) s)
              compileDeclsImpl info.all.toArray
            | .opaqueInfo _ =>
              modifyEnv (postponedCompileDeclsExt.modifyState · fun s => s.erase c)
              compileDeclsImpl #[c]
            | _ => unreachable!
      | _ => pure ()

  let decls := markRecDecls decls
  let manager ← getPassManager
  let isCheckEnabled := compiler.check.get (← getOptions)
  let decls ← runPassManagerPart .pure .pure "compilation (LCNF base)" manager.basePasses decls isCheckEnabled
  let decls ← runPassManagerPart .pure .pure "compilation (LCNF mono)" manager.monoPasses decls isCheckEnabled
  let sccs ← withTraceNode `Compiler.splitSCC (fun _ => return m!"Splitting up SCC") do
    splitScc decls
  sccs.mapM fun decls => do
    let decls ← runPassManagerPart .pure .impure "compilation (LCNF mono)" manager.monoPassesNoLambda decls isCheckEnabled
    withPhase .impure do
      let decls ← runPassManagerPart .impure .impure "compilation (LCNF impure)" manager.impurePasses decls isCheckEnabled

      if (← Lean.isTracingEnabledFor `Compiler.result) then
        for decl in decls do
          let decl ← normalizeFVarIds decl
          Lean.addTrace `Compiler.result m!"size: {decl.size}\n{← ppDecl' decl (← getPhase)}"

      -- TODO consider doing this in one go afterwards in a separate mapM and running clearPure to save memory
      -- or consider running clear? unclear
      profileitM Exception "compilation (IR)" (← getOptions) do
        let irDecls ← IR.toIR decls
        IR.compile irDecls
where
  runPassManagerPart (inPhase outPhase : Purity) (profilerName : String)
      (passes : Array Pass) (decls : Array (Decl inPhase)) (isCheckEnabled : Bool) :
      CompilerM (Array (Decl outPhase)) := do
    profileitM Exception profilerName (← getOptions) do
      let mut state : (pu : Purity) × Array (Decl pu) := ⟨inPhase, decls⟩
      for pass in passes do
        state ← withTraceNode `Compiler (fun _ => return m!"compiler phase: {pass.phase}, pass: {pass.name}") do
          let decls ← withPhase pass.phase do
            state.fst.withAssertPurity pass.phase.toPurity fun h => do
              pass.run (h ▸ state.snd)
          pure ⟨_, decls⟩
        withPhase pass.phaseOut <| checkpoint pass.name state.snd (isCheckEnabled || pass.shouldAlwaysRunCheck)
      let decls := state.fst.withAssertPurity outPhase fun h => h ▸ state.snd
      return decls

end PassManager

def compile (declNames : Array Name) : CoreM (Array (Array IR.Decl)) :=
  CompilerM.run <| PassManager.run declNames

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
