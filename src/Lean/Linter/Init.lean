/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
module

prelude
public import Lean.MonadEnv
public import Lean.EnvExtension
import Init.Data.Function

public section

namespace Lean.Linter

/-- Linter sets are represented as a map from linter name to set name,
to make it easy to look up which sets to check for enabling a linter.
-/
@[expose] def LinterSets := NameMap (Array Name)
  deriving EmptyCollection, Inhabited

/-- Insert a set into a `LinterSets` map.

`entry.1` is the name of the linter set,
`entry.2` contains the names of the set's linter options.
-/
def insertLinterSetEntry (map : LinterSets) (setName : Name) (options : NameSet) : LinterSets :=
  options.foldl (init := map) fun map linterName =>
    map.insert linterName ((map.getD linterName #[]).push setName)

/-- State of `linterSetsExt`.

`merged` is the queryable union of all sources (builtins folded in at env creation,
imported entries from oleans, and locally added entries). `localEntries` tracks entries
added in the current module so they can be exported into the olean.
-/
structure LinterSetsState where
  merged : LinterSets := {}
  localEntries : Array (Name × NameSet) := #[]
  deriving Inhabited

/-- Builtin linter sets registered from `builtin_initialize` blocks in core code.

Entries here are folded into every `LinterSetsState` produced by `linterSetsExt`, so they
participate in `getLinterValue` like any user-declared set.
-/
builtin_initialize builtinLinterSetsRef : IO.Ref (Array (Name × NameSet)) ← IO.mkRef #[]

/-- Register a builtin linter set entry. Only valid during initialization;
use `register_builtin_linter_set` rather than calling this directly. -/
def addBuiltinLinterSet (setName : Name) (linterNames : NameSet) : IO Unit := do
  builtinLinterSetsRef.modify (·.push (setName, linterNames))

builtin_initialize linterSetsExt :
    PersistentEnvExtension (Name × NameSet) (Name × NameSet) LinterSetsState ←
  registerPersistentEnvExtension {
    mkInitial := do
      let merged := (← builtinLinterSetsRef.get).foldl (init := {}) fun s (n, ms) =>
        insertLinterSetEntry s n ms
      return { merged, localEntries := #[] }
    addImportedFn := fun ess => do
      let s := (← builtinLinterSetsRef.get).foldl (init := {}) fun s (n, ms) =>
        insertLinterSetEntry s n ms
      let merged := ess.foldl (init := s) fun s es =>
        es.foldl (init := s) fun s (n, ms) => insertLinterSetEntry s n ms
      return { merged, localEntries := #[] }
    addEntryFn := fun st (n, ms) =>
      { merged := insertLinterSetEntry st.merged n ms, localEntries := st.localEntries.push (n, ms) }
    exportEntriesFn := fun st => st.localEntries
  }

/-- The `LinterOptions` structure is used to determine whether given linters are enabled.

This structure contains all the data required to do so, the `Options` set on the command line
or by the `set_option` command, and the `LinterSets` that have been declared.

A single structure holding this data is useful since we want `getLinterValue` to be a pure
function: determining the `LinterSets` would otherwise require a `MonadEnv` instance.
-/
structure LinterOptions where
  toOptions : Options
  linterSets : LinterSets

def LinterOptions.get [KVMap.Value α] (o : LinterOptions) := o.toOptions.get (α := α)
def LinterOptions.get? [KVMap.Value α] (o : LinterOptions) := o.toOptions.get? (α := α)

def _root_.Lean.Options.toLinterOptions [Monad m] [MonadEnv m] (o : Options) : m LinterOptions := do
  let linterSets := (linterSetsExt.getState (← getEnv)).merged
  return { toOptions := o, linterSets }

/-- Return the set of linter sets that this option is contained in. -/
def LinterOptions.getSet (o : LinterOptions) (opt : Lean.Option α) : Array Name :=
  o.linterSets.getD opt.name #[]

def getLinterOptions [Monad m] [MonadOptions m] [MonadEnv m] : m LinterOptions := do
  (← getOptions).toLinterOptions

register_builtin_option linter.all : Bool := {
  defValue := false
  descr := "enable all linters"
}

register_builtin_option linter.extra : Bool := {
  defValue := false
  descr := "enables the set of extra linters — linters that are turned off by default and \
    only available via `lake lint`. An extra linter early-returns unless this option is true."
}

/--
Global registry of options associated with environment linters.
These are precisely options, whose value will be snapshotted during `addDecl`.
-/
builtin_initialize envLinterOptionsRef : IO.Ref (Array (Lean.Option Bool)) ← IO.mkRef #[]

def addEnvLinterOption (opt : Lean.Option Bool) : IO Unit :=
  envLinterOptionsRef.modify (·.push opt)

def getLinterAll (o : LinterOptions) (defValue := linter.all.defValue) : Bool :=
    o.get linter.all.name defValue

def getLinterValue (opt : Lean.Option Bool) (o : LinterOptions) : Bool :=
  o.get opt.name (getLinterAll o <| (o.getSet opt).any (o.get? · == some true) || opt.defValue)

def isLinterEnabledByOptions (name : Name) (o : LinterOptions) : Bool :=
  o.get name (getLinterAll o <| (o.linterSets.getD name #[]).any (o.get? · == some true))

/--
Tag attached by `logLint` to every linter warning so consumers
(e.g. `Lean.Linter.recordLints`) can distinguish linter-produced messages
from other tagged messages such as named errors or unknown-identifier messages.
-/
def linterMessageTag : Name := `Lean.Linter._linter

def logLint [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
    (linterOption : Lean.Option Bool) (stx : Syntax) (msg : MessageData) : m Unit :=
  let disable := .note m!"This linter can be disabled with `set_option {linterOption.name} false`"
  logWarningAt stx <|
    .ofOriginatingSyntax stx <|
    .tagged linterOption.name <|
    .tagged linterMessageTag m!"{msg}{disable}"

/-- Returns true if `msg` was produced by `Lean.Linter.logLint` (and therefore by a linter). -/
def _root_.Lean.MessageData.isLinterMessage (msg : MessageData) : Bool :=
  msg.hasTag (· == linterMessageTag)

/--
If `linterOption` is enabled, print a linter warning message at the position determined by `stx`.

Whether a linter option is enabled or not is determined by the following sequence:
1. If it is set, then the value determines whether or not it is enabled.
2. Otherwise, if `linter.all` is set, then its value determines whether or not the option is enabled.
3. Otherwise, if any of the linter sets containing the option is enabled, it is enabled.
  (Only enabled linter sets are considered: explicitly disabling a linter set
  will revert the linters it contains to their default behavior.)
4. Otherwise, the default value determines whether or not it is enabled.
-/
def logLintIf [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m] [MonadEnv m]
    (linterOption : Lean.Option Bool) (stx : Syntax) (msg : MessageData) : m Unit := do
  if getLinterValue linterOption (← getLinterOptions) then logLint linterOption stx msg

abbrev EnvLinterSnapshot := NameMap Bool

/--
The `envLinterSnapshotExt` extension saves the state of all (Boolean-valued) `Lean.Option`s
associated with environment linters.
-/
builtin_initialize envLinterSnapshotExt : MapDeclarationExtension EnvLinterSnapshot ←
  -- `.asyncEnv`: the snapshot is written from within the declaration's own (async) elaboration
  -- via `addDecl`, so the modification happens on the declaration's async branch, not a parent.
  mkMapDeclarationExtension `envLinterSnapshotExt (asyncMode := .sync)

def getEnvLinterSnapshotEntry? (env : Environment) (declName optName : Name) : Option Bool :=
  envLinterSnapshotExt.find? env declName >>= (·.find? optName)
