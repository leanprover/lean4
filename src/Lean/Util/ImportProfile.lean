/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
module

prelude
public import Lean.Setup

public section

/-!
# Import profiles

Per-module and per-step costs of `importModules`, recorded in `EnvironmentHeader.importProfile?`
when the option `profiler.import` is set. Since the option is read while processing the header, it
must be given on the command line (`-Dprofiler.import=true`) or in the Lake configuration.

All times are `IO.monoNanosNow` readings, so ranges from the same process can be compared and
nested. Arrays indexed by `ModuleIdx` are parallel to `EnvironmentHeader.modules`.

Note that imported files are usually memory-mapped, so the cost of reading their contents is mostly
paid on first access, i.e. in whichever later step first touches the data.
-/

namespace Lean

/-- A range of `IO.monoNanosNow` readings. -/
structure MonoNanosRange where
  start : Nat
  stop  : Nat
deriving Inhabited, Repr

namespace MonoNanosRange

/-- Duration in nanoseconds. -/
def duration (r : MonoNanosRange) : Nat :=
  r.stop - r.start

/-- Runs `act`, also returning the range it took. -/
@[inline] def measure [Monad m] [MonadLiftT BaseIO m] (act : m α) : m (α × MonoNanosRange) := do
  let start ← IO.monoNanosNow
  let a ← act
  return (a, { start, stop := ← IO.monoNanosNow })

/-- Like `measure`, but only reads the clock if `enabled`. -/
@[inline] def measureIf [Monad m] [MonadLiftT BaseIO m] (enabled : Bool) (act : m α) :
    m (α × Option MonoNanosRange) := do
  if enabled then
    let (a, r) ← measure act
    return (a, some r)
  else
    return (← act, none)

end MonoNanosRange

/--
Cost of reading a module's `.olean*` parts. The range covers locating the files and reading all
parts.
-/
structure DataReadCost extends MonoNanosRange where
  olean         : MonoNanosRange
  /-- Present if the `.olean.server` part was read. -/
  oleanServer?  : Option MonoNanosRange
  /-- Present if the `.olean.private` part was read. -/
  oleanPrivate? : Option MonoNanosRange
deriving Inhabited, Repr

/--
Cost of reading a module's IR parts. The range covers locating the files and reading all parts.
Both parts are absent if the module has no `.ir.sig`, e.g. because it is not a `module`.
-/
structure IRReadCost extends MonoNanosRange where
  irSig? : Option MonoNanosRange
  ir?    : Option MonoNanosRange
deriving Inhabited, Repr

/-- Import costs of a single module, excluding environment extensions and initialization. -/
structure ModuleImportCost where
  /-- Present iff the module's `.olean*` data was loaded (`EffectiveImport.hasData`). -/
  readData?     : Option DataReadCost
  /-- Present iff the module's IR was needed, even if no IR parts exist. -/
  readIR?       : Option IRReadCost
  /--
  Adding the module's constants to the private constant map. The constants are read from the
  module's `.olean*` data if loaded, otherwise from its `.ir`, which contains no constants.
  -/
  privateConsts : MonoNanosRange
  /--
  Adding the module's extra constant names (e.g. auxiliary compiler declarations) to the
  constant-to-module map. These are read from the module's `.ir` if loaded for a `module`,
  otherwise from its `.olean`.
  -/
  extraConsts   : MonoNanosRange
  /-- Adding the module's constants to the public constant map; `module`s, exported imports only. -/
  publicConsts? : Option MonoNanosRange
deriving Inhabited, Repr

/-- Cost of running a single `[init]` declaration. -/
structure InitDeclCost extends MonoNanosRange where
  decl : Name
deriving Inhabited, Repr

/-- How a module's initialization was carried out. -/
inductive ExecKind where
  /-- The module's compiled initializer was called for the given phases. -/
  | native (phases : IRPhases)
  /--
  The `[init]` declarations in `ran` (nonempty) were run via the interpreter, which may still call
  into native code (see `interpreter.prefer_native`). `skipped` were not run as they are
  runtime-only while runtime initialization is disabled.
  -/
  | interpreted (ran : Array InitDeclCost) (skipped : Array Name)
  /-- All of the module's `[init]` declarations (nonempty) were skipped as runtime-only. -/
  | allSkipped (skipped : Array Name)
  /-- The module has neither a compiled initializer nor `[init]` declarations. -/
  | noInitDecls
  /-- The module's `[init]` declarations were already interpreted earlier in this process. -/
  | alreadyInterpreted
deriving Inhabited, Repr

/-- Whether no initialization code was run for the module. -/
def ExecKind.ranNothing : ExecKind → Bool
  | .native _ | .interpreted .. => false
  | .allSkipped _ | .noInitDecls | .alreadyInterpreted => true

/-- Initialization cost of a single module. The range includes looking up compiled initializers. -/
structure ModuleInitCost extends MonoNanosRange where
  exec : ExecKind
deriving Inhabited, Repr

/-- Import cost of a single persistent environment extension. The range covers `addImportedFn`. -/
structure ExtImportCost extends MonoNanosRange where
  /--
  Present if new persistent extensions or attributes were registered during this step (i.e. by
  initialization); covers setting up their imported entries and updating the attribute table.
  -/
  newExts? : Option MonoNanosRange
deriving Inhabited, Repr

/--
Costs of initializing persistent environment extensions from imported data, including running
`[init]` declarations. The range covers all of these steps.
-/
structure ExtsProfile extends MonoNanosRange where
  /-- Indexed by position in `persistentEnvExtensionsRef`. -/
  extensions      : Array ExtImportCost
  /-- Indexed by `ModuleIdx`. -/
  inits           : Array ModuleInitCost
  /-- Marking the final environment persistent; present iff the environment is leaked. -/
  markPersistent? : Option MonoNanosRange
deriving Inhabited, Repr

/-- Costs of `importModules`. The range covers the entire import, including loading plugins. -/
structure ImportProfile extends MonoNanosRange where
  /-- Determining the import closure and reading all files. -/
  readModules       : MonoNanosRange
  /-- Building the constant maps; see also `ModuleImportCost`. -/
  buildConstMaps    : MonoNanosRange
  /-- Setting up imported entries of persistent environment extensions. -/
  setEntries        : MonoNanosRange
  /-- Setting up imported IR entries of persistent environment extensions. -/
  setIREntries      : MonoNanosRange
  /-- Setting up imported entries for the language server; present iff importing at that level. -/
  setServerEntries? : Option MonoNanosRange
  /-- Marking the base environment persistent; present iff the environment is leaked. -/
  markPersistent?   : Option MonoNanosRange
  /-- Indexed by `ModuleIdx`. -/
  modules           : Array ModuleImportCost
  /-- Present iff environment extensions were initialized. -/
  exts?             : Option ExtsProfile
deriving Inhabited, Repr

end Lean
