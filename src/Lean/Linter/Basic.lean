/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
prelude
import Lean.Data.Options
import Lean.MonadEnv
import Lean.Log

namespace Lean.Linter

/-- Linter sets are represented as a map from linter name to set name,
to make it easy to look up which sets to check for enabling a linter.
-/
def LinterSets := NameMap (Array Name)
  deriving EmptyCollection, Inhabited

/-- Insert a set into a `LinterSets` map.

`entry.1` is the name of the linter set,
`entry.2` contains the names of the set's linter options.
-/
def insertLinterSetEntry (map : LinterSets) (entry : Name × Array Name) : LinterSets :=
  entry.2.foldl (init := map) fun map linterName =>
    map.insert linterName ((map.findD linterName #[]).push entry.1)

builtin_initialize linterSetsExt : SimplePersistentEnvExtension (Name × Array Name) LinterSets ← Lean.registerSimplePersistentEnvExtension {
  addImportedFn := mkStateFromImportedEntries insertLinterSetEntry {}
  addEntryFn := insertLinterSetEntry
  toArrayFn es := es.toArray
}

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
  o.linterSets.findD opt.name #[]

class MonadLinterOptions (m : Type → Type) where
  getLinterOptions : m LinterOptions

export MonadLinterOptions (getLinterOptions)

instance [Monad m] [MonadLinterOptions m] : MonadOptions m where
  getOptions := do return (← getLinterOptions).toOptions

instance [Monad m] [MonadOptions m] [MonadEnv m] : MonadLinterOptions m where
  getLinterOptions := do (← getOptions).toLinterOptions

instance [MonadLift m n] [MonadLinterOptions m] : MonadLinterOptions n where
  getLinterOptions := liftM (getLinterOptions : m _)

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
  let disable := m!"note: this linter can be disabled with `set_option {linterOption.name} false`"
  logWarningAt stx (.tagged linterOption.name m!"{msg}\n{disable}")

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
def logLintIf [Monad m] [MonadLog m] [AddMessageContext m] [MonadLinterOptions m]
    (linterOption : Lean.Option Bool) (stx : Syntax) (msg : MessageData) : m Unit := do
  if getLinterValue linterOption (← getLinterOptions) then logLint linterOption stx msg
