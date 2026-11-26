/-
Copyright (c) 2026 Lean FRO. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

prelude
public import Lean.Environment
import Lean.EnvExtension

namespace Lean

-- No public mutating interface as this is an implementation detail of `addDecl` and separated only
-- to avoid an import cycle.
builtin_initialize privateConstKindsExt : MapDeclarationExtension ConstantKind ←
  -- Use `sync` so we can add entries from anywhere without restrictions
  mkMapDeclarationExtension (asyncMode := .sync)

/--
Returns the kind of the declaration as originally declared instead of as exported. This information
is stored by `Lean.addDecl` and may be inaccurate if that function was circumvented. Returns `none`
if the declaration was not found.
-/
public def getOriginalConstKind? (env : Environment) (declName : Name) : Option ConstantKind := do
  -- Use `local` as for asynchronous decls from the current module, `findAsync?` below will yield
  -- the same result but potentially earlier (after `addConstAsync` instead of `addDecl`)
  privateConstKindsExt.find? (asyncMode := .local) env declName <|>
    (env.setExporting false |>.findAsync? declName).map (·.kind)

/--
Checks whether the declaration was originally declared as a definition; see also
`Lean.getOriginalConstKind?`. Returns `false` if the declaration was not found.
-/
public def wasOriginallyDefn (env : Environment) (declName : Name) : Bool :=
  getOriginalConstKind? env declName |>.map (· matches .defn) |>.getD false

/--
Checks whether the declaration was originally declared as a theorem; see also
`Lean.getOriginalConstKind?`. Returns `false` if the declaration was not found.
-/
public def wasOriginallyTheorem (env : Environment) (declName : Name) : Bool :=
  getOriginalConstKind? env declName |>.map (· matches .thm) |>.getD false

/-!
# Split modules

A module `M` may be split into a public file `M.lean` and a private file `M.private.lean`. In the
public file, `def` and `theorem` may omit their value, which is then added as an axiom. The private
file is elaborated as a continuation of the public file and must supply all omitted values; doing so
replaces each placeholder axiom with the actual declaration. Importers that only need the exported
`.olean` part therefore do not have to wait for the private file.
-/

public section

/-- Progress of a deferred declaration of a split module. -/
inductive DeferredDeclState where
  /-- Not yet supplied by the private file. -/
  | pending
  /-- The private file started supplying the declaration; the placeholder has been removed. -/
  | erased
  /-- The private file supplied the declaration. -/
  | filled
  deriving Inhabited, BEq

/-- A declaration in the public file of a split module whose value the private file must supply. -/
structure DeferredDecl where
  /-- Kind of the declaration to be supplied: `.defn`, `.opaque`, or `.thm`. -/
  kind : ConstantKind
  levelParams : List Name
  type : Expr
  state : DeferredDeclState := .pending
  deriving Inhabited

/-- Elaboration state of a split module. -/
structure SplitModuleState where
  /-- Whether elaboration has reached the private file. -/
  inPrivateFile : Bool := false
  deferred : NameMap DeferredDecl := {}
  /-- Deferred declaration names in declaration order. -/
  order : Array Name := #[]
  deriving Inhabited

builtin_initialize splitModuleExt : EnvExtension SplitModuleState ←
  registerEnvExtension (pure {})

namespace SplitModule

/-- Returns whether elaboration has reached the private file of a split module. -/
def isInPrivateFile (env : Environment) : Bool :=
  splitModuleExt.getState env |>.inPrivateFile

/-- Marks the end of the public file of a split module. -/
def startPrivateFile (env : Environment) : Environment :=
  splitModuleExt.modifyState env ({ · with inPrivateFile := true })

/-- Registers a declaration of the public file whose value the private file must supply. -/
def registerDeferredDecl (env : Environment) (declName : Name) (decl : DeferredDecl) :
    Environment :=
  splitModuleExt.modifyState env fun s => { s with
    deferred := s.deferred.insert declName decl
    order := s.order.push declName }

/-- Returns whether the current module is a split module with deferred declarations. -/
def hasDeferredDecls (env : Environment) : Bool :=
  !(splitModuleExt.getState env).order.isEmpty

/-- Returns the deferred declaration `declName`, if any. -/
def findDeferredDecl? (env : Environment) (declName : Name) : Option DeferredDecl :=
  splitModuleExt.getState env |>.deferred.find? declName

/--
Returns the deferred declaration `declName` if the private file is supplying or has supplied it.
-/
def findSupplied? (env : Environment) (declName : Name) : Option DeferredDecl := do
  let decl ← findDeferredDecl? env declName
  guard (decl.state != .pending)
  return decl

/-- Updates the state of the deferred declaration `declName`. -/
def setDeferredDeclState (env : Environment) (declName : Name) (state : DeferredDeclState) :
    Environment :=
  splitModuleExt.modifyState env fun s => { s with
    deferred := s.deferred.modify declName ({ · with state }) }

/--
If `declName` is a pending deferred declaration and elaboration has reached the private file,
removes its placeholder and returns it. The caller is then responsible for adding the declaration.
-/
def startFilling? (env : Environment) (declName : Name) : Option (DeferredDecl × Environment) := do
  guard (isInPrivateFile env)
  let decl ← findDeferredDecl? env declName
  guard (decl.state == .pending)
  let env := env.eraseLocalConst declName
  return (decl, setDeferredDeclState env declName .erased)

/--
Returns the deferred declarations that the private file has not started to supply, in order. A
declaration that it started to supply but did not finish already caused an error.
-/
def unfilledDecls (env : Environment) : Array Name :=
  let s := splitModuleExt.getState env
  s.order.filter fun n => s.deferred.find? n |>.any (·.state == .pending)

end SplitModule

end
