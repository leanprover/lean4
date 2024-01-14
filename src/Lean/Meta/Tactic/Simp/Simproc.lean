/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.ScopedEnvExtension
import Lean.Meta.DiscrTree
import Lean.Meta.Tactic.Simp.Types

namespace Lean.Meta.Simp

structure BuiltinSimprocs where
  keys  : HashMap Name (Array SimpTheoremKey) := {}
  procs : HashMap Name Simproc := {}
  deriving Inhabited

builtin_initialize builtinSimprocDeclsRef : IO.Ref BuiltinSimprocs ← IO.mkRef {}

structure SimprocDecl where
  declName : Name
  keys     : Array SimpTheoremKey
  deriving Inhabited

structure SimprocDeclExtState where
  builtin    : HashMap Name (Array SimpTheoremKey)
  newEntries : PHashMap Name (Array SimpTheoremKey) := {}
  deriving Inhabited

def SimprocDecl.lt (decl₁ decl₂ : SimprocDecl) : Bool :=
  Name.quickLt decl₁.declName decl₂.declName

builtin_initialize simprocDeclExt : PersistentEnvExtension SimprocDecl SimprocDecl SimprocDeclExtState ←
  registerPersistentEnvExtension {
    mkInitial       := return { builtin := (← builtinSimprocDeclsRef.get).keys }
    addImportedFn   := fun _ => return { builtin := (← builtinSimprocDeclsRef.get).keys }
    addEntryFn      := fun s d => { s with newEntries := s.newEntries.insert d.declName d.keys }
    exportEntriesFn := fun s =>
      let result := s.newEntries.foldl (init := #[]) fun result declName keys => result.push { declName, keys }
      result.qsort SimprocDecl.lt
  }

def getSimprocDeclKeys? (declName : Name) : CoreM (Option (Array SimpTheoremKey)) := do
  let env ← getEnv
  let keys? ← match env.getModuleIdxFor? declName with
    | some modIdx => do
      let some decl := (simprocDeclExt.getModuleEntries env modIdx).binSearch { declName, keys := #[] } SimprocDecl.lt
        | pure none
      pure (some decl.keys)
    | none        => pure ((simprocDeclExt.getState env).newEntries.find? declName)
  if let some keys := keys? then
    return some keys
  else
    return (simprocDeclExt.getState env).builtin.find? declName

def isBuiltinSimproc (declName : Name) : CoreM Bool := do
  let s := simprocDeclExt.getState (← getEnv)
  return s.builtin.contains declName

def isSimproc (declName : Name) : CoreM Bool :=
  return (← getSimprocDeclKeys? declName).isSome

def registerBuiltinSimproc (declName : Name) (key : Array SimpTheoremKey) (proc : Simproc) : IO Unit := do
  unless (← initializing) do
    throw (IO.userError s!"invalid builtin simproc declaration, it can only be registered during initialization")
  if (← builtinSimprocDeclsRef.get).keys.contains declName then
    throw (IO.userError s!"invalid builtin simproc declaration '{declName}', it has already been declared")
  builtinSimprocDeclsRef.modify fun { keys, procs } =>
    { keys := keys.insert declName key, procs := procs.insert declName proc }

def registerSimproc (declName : Name) (keys : Array SimpTheoremKey) : CoreM Unit := do
  let env ← getEnv
  unless (env.getModuleIdxFor? declName).isNone do
    throwError "invalid simproc declaration '{declName}', function declaration is in an imported module"
  if (← isSimproc declName) then
    throwError "invalid simproc declaration '{declName}', it has already been declared"
  modifyEnv fun env => simprocDeclExt.modifyState env fun s => { s with newEntries := s.newEntries.insert declName keys }

instance : BEq SimprocEntry where
  beq e₁ e₂ := e₁.declName == e₂.declName

instance : ToFormat SimprocEntry where
  format e := format e.declName

def Simprocs.erase (s : Simprocs) (declName : Name) : Simprocs :=
  { s with erased := s.erased.insert declName, simprocNames := s.simprocNames.erase declName }

builtin_initialize builtinSimprocsRef : IO.Ref Simprocs ← IO.mkRef {}

abbrev SimprocExtension := ScopedEnvExtension SimprocOLeanEntry SimprocEntry Simprocs

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

def addSimprocAttr (declName : Name) (kind : AttributeKind) (post : Bool) : CoreM Unit := do
  let proc ← getSimprocFromDecl declName
  let some keys ← getSimprocDeclKeys? declName |
    throwError "invalid [simproc] attribute, '{declName}' is not a simproc"
  simprocExtension.add { declName, post, keys, proc } kind

def addSimprocBuiltinAttr (declName : Name) (post : Bool) (proc : Simproc) : IO Unit := do
  let some keys := (← builtinSimprocDeclsRef.get).keys.find? declName |
    throw (IO.userError "invalid [builtin_simproc] attribute, '{declName}' is not a builtin simproc")
  if post then
    builtinSimprocsRef.modify fun s => { s with post := s.post.insertCore keys { declName, keys, post, proc } }
  else
    builtinSimprocsRef.modify fun s => { s with pre := s.pre.insertCore keys { declName, keys, post, proc } }

def getSimprocs : CoreM Simprocs :=
  return simprocExtension.getState (← getEnv)

def Simprocs.add (s : Simprocs) (declName : Name) (post : Bool) : CoreM Simprocs := do
  let proc ←
    try
      getSimprocFromDecl declName
    catch e =>
      if (← isBuiltinSimproc declName) then
        let some proc := (← builtinSimprocDeclsRef.get).procs.find? declName
          | throwError "invalid [simproc] attribute, '{declName}' is not a simproc"
        pure proc
      else
        throw e
  let some keys ← getSimprocDeclKeys? declName |
    throwError "invalid [simproc] attribute, '{declName}' is not a simproc"
  if post then
    return { s with post := s.post.insertCore keys { declName, keys, post, proc } }
  else
    return { s with pre := s.pre.insertCore keys { declName, keys, post, proc } }

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

def simproc? (post : Bool) (s : SimprocTree) (erased : PHashSet Name) (e : Expr) : SimpM (Option Step) := do
  let candidates ← s.getMatchWithExtra e (getDtConfig (← getConfig))
  if candidates.isEmpty then
    let tag := if post then "post" else "pre"
    trace[Debug.Meta.Tactic.simp] "no {tag}-simprocs found for {e}"
    return none
  else
    for (simprocEntry, numExtraArgs) in candidates do
      unless erased.contains simprocEntry.declName do
        if let some step ← simprocEntry.try? numExtraArgs e then
          trace[Debug.Meta.Tactic.simp] "simproc result {e} => {step.result.expr}"
          recordSimpTheorem (.decl simprocEntry.declName post)
          return some step
    return none

register_builtin_option simprocs : Bool := {
  defValue := true
  descr    := "Enable/disable `simproc`s (simplification procedures)."
}

def preSimproc? (e : Expr) : SimpM (Option Step) := do
  unless simprocs.get (← getOptions) do return none
  let s := (← getMethods).simprocs
  simproc? (post := false) s.pre s.erased e

def postSimproc? (e : Expr) : SimpM (Option Step) := do
  unless simprocs.get (← getOptions) do return none
  let s := (← getMethods).simprocs
  simproc? (post := true) s.post s.erased e

end Lean.Meta.Simp
