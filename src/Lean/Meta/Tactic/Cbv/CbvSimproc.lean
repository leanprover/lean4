/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module
prelude
public import Lean.Compiler.InitAttr
public import Lean.ScopedEnvExtension
public import Lean.Meta.Sym.Simp.SimpM
public import Lean.Meta.Sym.Simp.Result
public import Lean.Meta.Sym.Simp.App
public import Lean.Meta.Sym.Simp.DiscrTree
public import Lean.Meta.Sym.Pattern

public section
namespace Lean.Meta.Tactic.Cbv
open Lean.Meta.Sym
open Lean.Meta.Sym.Simp

inductive CbvSimprocPhase where
  | pre | eval | post
  deriving Inhabited, BEq, Hashable, Repr

instance : ToExpr CbvSimprocPhase where
  toExpr
    | .pre  => mkConst ``CbvSimprocPhase.pre
    | .eval => mkConst ``CbvSimprocPhase.eval
    | .post => mkConst ``CbvSimprocPhase.post
  toTypeExpr := mkConst ``CbvSimprocPhase

structure CbvSimprocOLeanEntry where
  declName : Name
  phase    : CbvSimprocPhase := .post
  keys     : Array DiscrTree.Key := #[]
  deriving Inhabited

structure CbvSimprocEntry extends CbvSimprocOLeanEntry where
  proc : Simproc

instance : BEq CbvSimprocEntry where
  beq e₁ e₂ := e₁.declName == e₂.declName

instance : ToFormat CbvSimprocEntry where
  format e := format e.declName

structure CbvSimprocs where
  pre          : DiscrTree CbvSimprocEntry := {}
  eval         : DiscrTree CbvSimprocEntry := {}
  post         : DiscrTree CbvSimprocEntry := {}
  simprocNames : PHashSet Name := {}
  erased       : PHashSet Name := {}
  deriving Inhabited

def CbvSimprocs.addCore (s : CbvSimprocs) (keys : Array DiscrTree.Key) (declName : Name)
    (phase : CbvSimprocPhase) (proc : Simproc) : CbvSimprocs :=
  let entry : CbvSimprocEntry := { declName, phase, keys, proc }
  let s := { s with simprocNames := s.simprocNames.insert declName, erased := s.erased.erase declName }
  match phase with
  | .pre  => { s with pre  := s.pre.insertKeyValue keys entry }
  | .eval => { s with eval := s.eval.insertKeyValue keys entry }
  | .post => { s with post := s.post.insertKeyValue keys entry }

def CbvSimprocs.erase (s : CbvSimprocs) (declName : Name) : CbvSimprocs :=
  { s with erased := s.erased.insert declName, simprocNames := s.simprocNames.erase declName }

structure BuiltinCbvSimprocs where
  keys  : Std.HashMap Name (CbvSimprocPhase × Array DiscrTree.Key) := {}
  procs : Std.HashMap Name Simproc := {}
  deriving Inhabited

builtin_initialize builtinCbvSimprocDeclsRef : IO.Ref BuiltinCbvSimprocs ← IO.mkRef {}

def registerBuiltinCbvSimproc (declName : Name) (phase : CbvSimprocPhase)
    (keys : Array DiscrTree.Key) (proc : Simproc) : IO Unit := do
  unless (← initializing) do
    throw (IO.userError s!"Invalid builtin cbv simproc declaration: \
      It can only be registered during initialization")
  if (← builtinCbvSimprocDeclsRef.get).keys.contains declName then
    throw (IO.userError s!"Invalid builtin cbv simproc declaration \
      `{privateToUserName declName}`: It has already been declared")
  builtinCbvSimprocDeclsRef.modify fun { keys := ks, procs } =>
    { keys := ks.insert declName (phase, keys), procs := procs.insert declName proc }

structure CbvSimprocDecl where
  declName : Name
  phase    : CbvSimprocPhase
  keys     : Array DiscrTree.Key
  deriving Inhabited

def CbvSimprocDecl.lt (d₁ d₂ : CbvSimprocDecl) : Bool :=
  Name.quickLt d₁.declName d₂.declName

structure CbvSimprocDeclExtState where
  builtin    : Std.HashMap Name (CbvSimprocPhase × Array DiscrTree.Key)
  newEntries : PHashMap Name (CbvSimprocPhase × Array DiscrTree.Key) := {}
  deriving Inhabited

builtin_initialize cbvSimprocDeclExt :
    PersistentEnvExtension CbvSimprocDecl CbvSimprocDecl CbvSimprocDeclExtState ←
  registerPersistentEnvExtension {
    mkInitial       := return { builtin := (← builtinCbvSimprocDeclsRef.get).keys }
    addImportedFn   := fun _ => return { builtin := (← builtinCbvSimprocDeclsRef.get).keys }
    addEntryFn      := fun s d =>
      { s with newEntries := s.newEntries.insert d.declName (d.phase, d.keys) }
    exportEntriesFn := fun s =>
      let result := s.newEntries.foldl (init := #[]) fun result declName (phase, keys) =>
        result.push { declName, phase, keys }
      result.qsort CbvSimprocDecl.lt
  }

def getCbvSimprocDeclInfo? (declName : Name) :
    CoreM (Option (CbvSimprocPhase × Array DiscrTree.Key)) := do
  let env ← getEnv
  let info? ← match env.getModuleIdxFor? declName with
    | some modIdx => do
      let sentinel : CbvSimprocDecl := { declName, phase := .post, keys := #[] }
      let some decl :=
        (cbvSimprocDeclExt.getModuleEntries env modIdx).binSearch sentinel CbvSimprocDecl.lt
        | pure none
      pure (some (decl.phase, decl.keys))
    | none => pure ((cbvSimprocDeclExt.getState env).newEntries.find? declName)
  if let some info := info? then
    return some info
  else
    return (cbvSimprocDeclExt.getState env).builtin[declName]?

def isCbvSimproc (declName : Name) : CoreM Bool :=
  return (← getCbvSimprocDeclInfo? declName).isSome

def isBuiltinCbvSimproc (declName : Name) : CoreM Bool := do
  return (cbvSimprocDeclExt.getState (← getEnv)).builtin.contains declName

def registerCbvSimproc (declName : Name) (phase : CbvSimprocPhase)
    (keys : Array DiscrTree.Key) : CoreM Unit := do
  let env ← getEnv
  unless (env.getModuleIdxFor? declName).isNone do
    throwError "Invalid cbv simproc declaration `{.ofConstName declName}`: \
      It is declared in an imported module"
  if (← isCbvSimproc declName) then
    throwError "Invalid cbv simproc declaration `{.ofConstName declName}`: \
      It has already been declared"
  modifyEnv fun env => cbvSimprocDeclExt.modifyState env fun s =>
    { s with newEntries := s.newEntries.insert declName (phase, keys) }

abbrev CbvSimprocExtension := ScopedEnvExtension CbvSimprocOLeanEntry CbvSimprocEntry CbvSimprocs

unsafe def getCbvSimprocFromDeclImpl (declName : Name) : ImportM Simproc := do
  let ctx ← read
  match ctx.env.find? declName with
  | none      => throw <| IO.userError ("Unknown constant `" ++ toString declName ++ "`")
  | some info =>
    match info.type with
    | .const ``Simproc _ =>
      IO.ofExcept <| ctx.env.evalConst Simproc ctx.opts declName
    | _ => throw <| IO.userError s!"Cbv simproc `{privateToUserName declName}` has an \
        unexpected type: Expected `Simproc`, but found `{info.type}`"

@[implemented_by getCbvSimprocFromDeclImpl]
opaque getCbvSimprocFromDecl (declName : Name) : ImportM Simproc

def toCbvSimprocEntry (e : CbvSimprocOLeanEntry) : ImportM CbvSimprocEntry := do
  return { toCbvSimprocOLeanEntry := e, proc := (← getCbvSimprocFromDecl e.declName) }

builtin_initialize builtinCbvSimprocsRef : IO.Ref CbvSimprocs ← IO.mkRef {}

builtin_initialize cbvSimprocExtension : CbvSimprocExtension ←
  registerScopedEnvExtension {
    name         := `cbvSimprocExt
    mkInitial    := builtinCbvSimprocsRef.get
    ofOLeanEntry := fun _ => toCbvSimprocEntry
    toOLeanEntry := fun e => e.toCbvSimprocOLeanEntry
    addEntry     := fun s e => s.addCore e.keys e.declName e.phase e.proc
  }

def eraseCbvSimprocAttr (declName : Name) : AttrM Unit := do
  let s := cbvSimprocExtension.getState (← getEnv)
  unless s.simprocNames.contains declName do
    throwError "`{.ofConstName declName}` does not have a [cbv_simproc] attribute"
  modifyEnv fun env => cbvSimprocExtension.modifyState env fun s => s.erase declName

def addCbvSimprocAttrCore (declName : Name) (kind : AttributeKind)
    (phase : CbvSimprocPhase) : CoreM Unit := do
  let proc ← getCbvSimprocFromDecl declName
  let some (_, keys) ← getCbvSimprocDeclInfo? declName |
    throwError "Invalid `[cbv_simproc]` attribute: \
      `{.ofConstName declName}` is not a cbv simproc"
  cbvSimprocExtension.add { declName, phase, keys, proc } kind

def parseCbvSimprocPhase (stx : Syntax) : CbvSimprocPhase :=
  if stx.isNone then .post
  else
    let inner := stx[0]
    if inner.getKind == `Lean.Parser.Tactic.simpPre then .pre
    else if inner.getKind == `Lean.Parser.cbvSimprocEval then .eval
    else .post

def addCbvSimprocAttr (declName : Name) (stx : Syntax)
    (attrKind : AttributeKind) : AttrM Unit := do
  ensureAttrDeclIsMeta `cbvSimprocAttr declName attrKind
  let go : MetaM Unit := do
    addCbvSimprocAttrCore declName attrKind (parseCbvSimprocPhase stx[1])
  discard <| go.run {} {}

def addCbvSimprocBuiltinAttrCore (ref : IO.Ref CbvSimprocs) (declName : Name)
    (phase : CbvSimprocPhase) (proc : Simproc) : IO Unit := do
  let some (_, keys) := (← builtinCbvSimprocDeclsRef.get).keys[declName]? |
    throw (IO.userError s!"Invalid `[builtin_cbv_simproc]` attribute: \
      `{privateToUserName declName}` is not a builtin cbv simproc")
  ref.modify fun s => s.addCore keys declName phase proc

def addCbvSimprocBuiltinAttr (declName : Name) (phase : CbvSimprocPhase)
    (proc : Simproc) : IO Unit :=
  addCbvSimprocBuiltinAttrCore builtinCbvSimprocsRef declName phase proc

private def addBuiltinCbvSimproc (declName : Name) (stx : Syntax) : AttrM Unit := do
  let go : MetaM Unit := do
    let phase := parseCbvSimprocPhase stx[1]
    let val := mkAppN (mkConst ``addCbvSimprocBuiltinAttr)
      #[toExpr declName, toExpr phase, mkConst declName]
    let initDeclName ← mkFreshUserName (declName ++ `declare)
    declareBuiltin initDeclName val
  go.run' {}

builtin_initialize
  registerBuiltinAttribute {
    ref             := by exact decl_name%
    name            := `cbvSimprocAttr
    descr           := "Cbv simplification procedure"
    applicationTime := AttributeApplicationTime.afterCompilation
    add             := fun declName stx attrKind => addCbvSimprocAttr declName stx attrKind
    erase           := fun declName => eraseCbvSimprocAttr declName
  }

builtin_initialize
  registerBuiltinAttribute {
    ref             := by exact decl_name%
    name            := `cbvSimprocBuiltinAttr
    descr           := "Builtin cbv simplification procedure"
    applicationTime := AttributeApplicationTime.afterCompilation
    erase           := fun _ => throwError "Not implemented yet, [-builtin_cbv_simproc]"
    add             := fun declName stx _ => addBuiltinCbvSimproc declName stx
  }

def getCbvSimprocs : CoreM CbvSimprocs :=
  return cbvSimprocExtension.getState (← getEnv)

def cbvSimprocDispatch (tree : DiscrTree CbvSimprocEntry)
    (erased : PHashSet Name) : Simproc := fun e => do
  let candidates := Sym.getMatchWithExtra tree e
  if candidates.isEmpty then
    return .rfl
  for (entry, numExtra) in candidates do
    unless erased.contains entry.declName do
      let result ← if numExtra == 0 then
        entry.proc e
      else
        simpOverApplied e numExtra entry.proc
      if !result.isRfl then
        return result
  return .rfl

end Lean.Meta.Tactic.Cbv
