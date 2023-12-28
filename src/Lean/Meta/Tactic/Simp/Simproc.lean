/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.ScopedEnvExtension
import Lean.Meta.DiscrTree
import Lean.Meta.Tactic.Simp.Types

namespace Lean.Meta.Simp

abbrev Simproc := Expr → SimpM (Option Step)

structure SimprocOLeanEntry where
  /-- Name of a declaration stored in the environment which has type `Simproc`. -/
  declName : Name
  post     : Bool := true
  priority : Nat  := eval_prio default
  keys     : Array SimpTheoremKey := #[]
  deriving Inhabited

structure SimprocEntry extends SimprocOLeanEntry where
  /--
  Recall that we cannot store `Simproc` into .olean files because it is a closure.
  Given `SimprocOLeanEntry.declName`, we convert it into a `Simproc` by using the unsafe function `evalConstCheck`.
  -/
  proc : Simproc

instance : BEq SimprocEntry where
  beq e₁ e₂ := e₁.declName == e₂.declName

instance : ToFormat SimprocEntry where
  format e := format e.declName

abbrev SimprocTree := DiscrTree SimprocEntry

structure SimprocState where
  pre          : SimprocTree   := DiscrTree.empty
  post         : SimprocTree   := DiscrTree.empty
  simprocNames : PHashSet Name := {}
  erased       : PHashSet Name := {}
  deriving Inhabited

def SimprocState.erase (s : SimprocState) (declName : Name) : SimprocState :=
  { s with erased := s.erased.insert declName, simprocNames := s.simprocNames.erase declName }

builtin_initialize builtinSimprocsRef : IO.Ref SimprocState ← IO.mkRef {}

abbrev SimprocExtension := ScopedEnvExtension SimprocOLeanEntry SimprocEntry SimprocState

unsafe def getSimprocFromDeclImpl (declName : Name) : ImportM Simproc := do
  let ctx ← read
  match ctx.env.evalConstCheck Simproc ctx.opts ``Lean.Meta.Simp.Simproc declName with
  | .ok proc  => return proc
  | .error ex => throw (IO.userError ex)

@[implemented_by getSimprocFromDeclImpl]
opaque getSimprocFromDecl (declName: Name) : ImportM Simproc

def toSimprocEntry (e : SimprocOLeanEntry) : ImportM SimprocEntry := do
  return { toSimprocOLeanEntry := e, proc := (← getSimprocFromDecl e.declName) }

builtin_initialize simprocExtension : SimprocExtension ←
  registerScopedEnvExtension {
    name          := `simproc
    mkInitial     := builtinSimprocsRef.get
    ofOLeanEntry  := fun _ => toSimprocEntry
    toOLeanEntry  := fun e => e.toSimprocOLeanEntry
    addEntry      := fun s e =>
      if e.post then
        { s with post := s.post.insertCore e.keys e }
      else
        { s with pre := s.pre.insertCore e.keys e }
  }

def eraseSimprocAttr (declName : Name) : AttrM Unit := do
  let s := simprocExtension.getState (← getEnv)
  unless s.simprocNames.contains declName do
    throwError "'{declName}' does not have [simproc] attribute"
  modifyEnv fun env => simprocExtension.modifyState env fun s => s.erase declName

def addSimprocAttr (declName : Name) (kind : AttributeKind) (post : Bool) (priority : Nat) (pattern : Expr) : MetaM Unit := do
  let proc ← getSimprocFromDecl declName
  let keys ← DiscrTree.mkPath pattern simpDtConfig
  simprocExtension.add { declName, post, priority, keys, proc } kind

def getSimprocState : CoreM SimprocState :=
  return simprocExtension.getState (← getEnv)

def SimprocEntry.try? (s : SimprocEntry) (numExtraArgs : Nat) (e : Expr) : SimpM (Option Step) := do
  let mut extraArgs := #[]
  let mut e := e
  for _ in [:numExtraArgs] do
    extraArgs := extraArgs.push e.appArg!
    e := e.appFn!
  extraArgs := extraArgs.reverse
  match (← s.proc e) with
  | none => return none
  | some step => return some (← step.addExtraArgs extraArgs)

def simproc? (tag : String) (s : SimprocTree) (erased : PHashSet Name) (e : Expr) : SimpM (Option Step) := do
  let candidates ← s.getMatchWithExtra e (getDtConfig (← getConfig))
  if candidates.isEmpty then
    trace[Debug.Meta.Tactic.simp] "no {tag}-simprocs found for {e}"
    return none
  else
    let candidates := candidates.insertionSort fun e₁ e₂ => e₁.1.priority > e₂.1.priority
    for (simprocEntry, numExtraArgs) in candidates do
      unless erased.contains simprocEntry.declName do
        if let some step ← simprocEntry.try? numExtraArgs e then
          trace[Debug.Meta.Tactic.simp] "simproc result {e} => {step.result.expr}"
          return some step
    return none

def preSimproc? (e : Expr) : SimpM (Option Step) := do
  if !(← getConfig).simproc then return none
  let s := simprocExtension.getState (← getEnv)
  simproc? "pre" s.pre s.erased e

def postSimproc? (e : Expr) : SimpM (Option Step) := do
  if !(← getConfig).simproc then return none
  let s := simprocExtension.getState (← getEnv)
  simproc? "post" s.post s.erased e

end Lean.Meta.Simp
