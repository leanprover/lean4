/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
module

prelude
public import Lean.MonadEnv

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

builtin_initialize linterSetsExt : SimplePersistentEnvExtension (Name × NameSet) LinterSets ← Lean.registerSimplePersistentEnvExtension {
  addImportedFn := mkStateFromImportedEntries (Function.uncurry <| insertLinterSetEntry ·) {}
  addEntryFn := (Function.uncurry <| insertLinterSetEntry ·)
  toArrayFn es := es.toArray
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
  let linterSets := linterSetsExt.getState (← getEnv)
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

def getLinterAll (o : LinterOptions) (defValue := linter.all.defValue) : Bool :=
    o.get linter.all.name defValue

def getLinterValue (opt : Lean.Option Bool) (o : LinterOptions) : Bool :=
  o.get opt.name (getLinterAll o <| (o.getSet opt).any (o.get? · == some true) || opt.defValue)

def logLint [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
    (linterOption : Lean.Option Bool) (stx : Syntax) (msg : MessageData) : m Unit :=
  let disable := .note m!"This linter can be disabled with `set_option {linterOption.name} false`"
  logWarningAt stx (.tagged linterOption.name m!"{msg}{disable}")

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
