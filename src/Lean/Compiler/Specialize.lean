/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Basic
import Lean.Attributes

namespace Lean.Compiler

inductive SpecializeAttributeKind where
  | specialize | nospecialize
  deriving Inhabited, BEq

builtin_initialize nospecializeAttr : TagAttribute ←
  registerTagAttribute `nospecialize "mark definition to never be specialized"

private def elabSpecArgs (declName : Name) (args : Array Syntax) : MetaM (Array Nat) := do
  if args.isEmpty then return #[]
  let info ← getConstInfo declName
  Meta.forallTelescopeReducing info.type fun xs _ => do
    let argNames ← xs.mapM fun x => x.fvarId!.getUserName
    let mut result := #[]
    for arg in args do
      if let some idx := arg.isNatLit? then
        if idx == 0 then throwErrorAt arg "invalid specialization argument index, index must be greater than 0"
        let idx := idx - 1
        if h : idx >= argNames.size then
          throwErrorAt arg "invalid argument index, `{declName}` has #{argNames.size} arguments"
        else
          if result.contains idx then throwErrorAt arg "invalid specialization argument index, `{argNames[idx]}` has already been specified as a specialization candidate"
          result := result.push idx
      else
        let argName := arg.getId
        if let some idx := argNames.idxOf? argName then
          if result.contains idx then throwErrorAt arg "invalid specialization argument name `{argName}`, it has already been specified as a specialization candidate"
          result := result.push idx
        else
          throwErrorAt arg "invalid specialization argument name `{argName}`, `{declName}` does have an argument with this name"
    return result.qsort (·<·)

builtin_initialize specializeAttr : ParametricAttribute (Array Nat) ←
  registerParametricAttribute {
    name := `specialize
    descr := "mark definition to always be specialized"
    getParam := fun declName stx => do
      let args := stx[1].getArgs
      elabSpecArgs declName args |>.run'
  }

def getSpecializationArgs? (env : Environment) (declName : Name) : Option (Array Nat) :=
  specializeAttr.getParam? env declName

def hasSpecializeAttribute (env : Environment) (declName : Name) : Bool :=
  getSpecializationArgs? env declName |>.isSome

def hasNospecializeAttribute (env : Environment) (declName : Name) : Bool :=
  nospecializeAttr.hasTag env declName

/- TODO: the rest of the file is for the old / current code generator. We should remove it as soon as we move to the new one. -/

@[export lean_has_specialize_attribute]
partial def hasSpecializeAttributeOld (env : Environment) (n : Name) : Bool :=
  match specializeAttr.getParam? env n with
  | some _ => true
  | none   => if n.isInternal then hasSpecializeAttributeOld env n.getPrefix else false -- TODO: remove recursion after we move to new compiler

@[export lean_has_nospecialize_attribute]
partial def hasNospecializeAttributeOld (env : Environment) (n : Name) : Bool :=
  nospecializeAttr.hasTag env n ||
  (n.isInternal && hasNospecializeAttributeOld env n.getPrefix) -- TODO: remove recursion after we move to new compiler

inductive SpecArgKind where
  | fixed
  | fixedNeutral -- computationally neutral
  | fixedHO      -- higher order
  | fixedInst    -- type class instance
  | other
  deriving Inhabited

structure SpecInfo where
  mutualDecls : List Name
  argKinds : List SpecArgKind
  deriving Inhabited

structure SpecState where
  specInfo : SMap Name SpecInfo := {}
  cache    : SMap Expr Name := {}
  deriving Inhabited

inductive SpecEntry where
  | info (name : Name) (info : SpecInfo)
  | cache (key : Expr) (fn : Name)
  deriving Inhabited

namespace SpecState

def addEntry (s : SpecState) (e : SpecEntry) : SpecState :=
  match e with
  | SpecEntry.info name info => { s with specInfo := s.specInfo.insert name info }
  | SpecEntry.cache key fn   => { s with cache    := s.cache.insert key fn }

def switch : SpecState → SpecState
  | ⟨m₁, m₂⟩ => ⟨m₁.switch, m₂.switch⟩

end SpecState

builtin_initialize specExtension : SimplePersistentEnvExtension SpecEntry SpecState ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := SpecState.addEntry,
    addImportedFn := fun es => (mkStateFromImportedEntries SpecState.addEntry {} es).switch
    asyncMode     := .sync  -- compilation is non-parallel anyway
    replay?       := some <| SimplePersistentEnvExtension.replayOfFilter (fun
      | s, .info n _ => !s.specInfo.contains n
      | s, .cache key _ => !s.cache.contains key) SpecState.addEntry
  }

@[export lean_add_specialization_info]
def addSpecializationInfo (env : Environment) (fn : Name) (info : SpecInfo) : Environment :=
  specExtension.addEntry env (SpecEntry.info fn info)

@[export lean_get_specialization_info]
def getSpecializationInfo (env : Environment) (fn : Name) : Option SpecInfo :=
  (specExtension.getState env).specInfo.find? fn

@[export lean_cache_specialization]
def cacheSpecialization (env : Environment) (e : Expr) (fn : Name) : Environment :=
  specExtension.addEntry env (SpecEntry.cache e fn)

@[export lean_get_cached_specialization]
def getCachedSpecialization (env : Environment) (e : Expr) : Option Name :=
  (specExtension.getState env).cache.find? e

end Lean.Compiler
