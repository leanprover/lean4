/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Data.Array.BinSearch
public import Init.Data.Stream
public import Init.System.Promise
public import Lean.Data.NameTrie
public import Lean.Setup
public import Lean.LocalContext
public import Lean.Util.Path
public import Lean.Util.FindExpr
public import Lean.Util.Profile
public import Lean.Util.InstantiateLevelParams
public import Lean.Util.FoldConsts
public import Lean.PrivateName
public import Lean.LoadDynlib
public import Init.Dynamic
import Init.Data.Slice
import Init.Data.String.TakeDrop

public section

/-!
# Note [Environment Branches]

The kernel environment type `Lean.Kernel.Environment` enforces a linear order on the addition of
declarations: `addDeclCore` takes an environment and returns a new one, assuming type checking
succeeded. On the other hand, the metaprogramming-level `Lean.Environment` wrapper must allow for
*branching* environment transformations so that multiple declarations can be elaborated
concurrently while still being able to access information about preceding declarations that have
also been branched out as soon as they are available.

The basic function to introduce such branches is `addConstAsync`, which takes an environment and
returns a structure containing two environments: one for the "main" branch that can be used in
further branching and eventually contains all the declarations of the file and one for the "async"
branch that can be used concurrently to the main branch to elaborate and add the declaration for
which the branch was introduced. Branches are "joined" back together implicitly via the kernel
environment, which as mentioned cannot be changed concurrently: when the main branch first tries to
access it, evaluation is blocked until the kernel environment on the async branch is complete.
Thus adding two declarations A and B concurrently can be visualized like this:
```text
o addConstAsync A
|\
| \
|  \
o addConstAsync B
|\   \
| \   o elaborate A
|  \  |
|   o elaborate B
|   | |
|   | o addDeclCore A
|   |/
|   o addDeclCore B
|  /
| /
|/
o .olean serialization calls Environment.toKernelEnv
```
While each edge represents a `Lean.Environment` that has its own view of the state of the module,
the kernel environment really lives only in the right-most path, with all other paths merely holding
an unfulfilled `Task` representing it and where forcing that task leads to the back-edges joining
paths back together.
-/

namespace Lean
register_builtin_option debug.skipKernelTC : Bool := {
  defValue := false
  descr    := "skip kernel type checker. WARNING: setting this option to true may compromise soundness because your proofs will not be checked by the Lean kernel"
}

/-- Opaque environment extension state. -/
opaque EnvExtensionStateSpec : (α : Type) × Inhabited α := ⟨Unit, ⟨()⟩⟩
@[expose] def EnvExtensionState : Type := EnvExtensionStateSpec.fst
instance : Inhabited EnvExtensionState := EnvExtensionStateSpec.snd

@[expose] def ModuleIdx := Nat
  deriving BEq, ToString, Hashable

abbrev ModuleIdx.toNat (midx : ModuleIdx) : Nat := midx

instance : Inhabited ModuleIdx where default := (0 : Nat)

instance : GetElem (Array α) ModuleIdx α (fun a i => i.toNat < a.size) where
  getElem a i h := a[i.toNat]

instance : GetElem? (Array α) ModuleIdx α (fun a i => i.toNat < a.size) where
  getElem? a i := a[i.toNat]?
  getElem! a i := a[i.toNat]!

abbrev ConstMap := SMap Name ConstantInfo

/--
  A compacted region holds multiple Lean objects in a contiguous memory region, which can be read/written to/from disk.
  Objects inside the region do not have reference counters and cannot be freed individually. The contents of .olean
  files are compacted regions. -/
@[expose] def CompactedRegion := USize

@[extern "lean_compacted_region_is_memory_mapped"]
opaque CompactedRegion.isMemoryMapped : CompactedRegion → Bool

/-- Size in bytes. -/
@[extern "lean_compacted_region_size"]
opaque CompactedRegion.size : CompactedRegion → USize

/-- Free a compacted region and its contents. No live references to the contents may exist at the time of invocation. -/
@[extern "lean_compacted_region_free"]
unsafe opaque CompactedRegion.free : CompactedRegion → IO Unit

/-- Opaque persistent environment extension entry. -/
opaque EnvExtensionEntrySpec : NonemptyType.{0}
@[expose] def EnvExtensionEntry : Type := EnvExtensionEntrySpec.type
instance : Nonempty EnvExtensionEntry := EnvExtensionEntrySpec.property

/-- Content of a .olean file.
   We use `compact.cpp` to generate the image of this object in disk. -/
structure ModuleData where
  /-- Participating in the module system? -/
  isModule        : Bool
  imports         : Array Import
  /--
  `constNames` contains all constant names in `constants`.
  This information is redundant. It is equal to `constants.map fun c => c.name`,
  but it improves the performance of `importModules`. `perf` reports that 12% of the
  runtime was being spent on `ConstantInfo.name` when importing a file containing only `import Lean`
  -/
  constNames      : Array Name
  constants       : Array ConstantInfo
  /--
  Extra entries for the `const2ModIdx` map in the `Environment` object.
  The code generator creates auxiliary declarations that are not in the
  mapping `constants`, but we want to know in which module they were generated.
  -/
  extraConstNames : Array Name
  entries         : Array (Name × Array EnvExtensionEntry)
  deriving Inhabited

/-- Phases for which some IR is available for execution. -/
inductive IRPhases where
  /-- Available for execution in the final native code. -/
  | runtime
  /-- Available for execution during elaboration. -/
  | comptime
  /-- Available during run time and compile time. -/
  | all
deriving Inhabited, BEq, Repr

/-- Import including information resulting from processing of the entire import DAG. -/
structure EffectiveImport extends Import where
  /-- Phases for which the import's IR is available. -/
  irPhases : IRPhases
deriving Inhabited

/-- Environment fields that are not used often. -/
structure EnvironmentHeader where
  /--
  The trust level used by the kernel. For example,
  the kernel assumes imported constants are type correct when the trust level is greater than zero.
  -/
  trustLevel   : UInt32       := 0
  /--
  Name of the module being compiled.
  -/
  mainModule   : Name         := default
  /-- Participating in the module system? -/
  isModule     : Bool         := false
  /-- Direct imports -/
  imports      : Array Import := #[]
  /-- Compacted regions for all imported modules. Objects in compacted memory regions do no require any memory management. -/
  regions      : Array CompactedRegion := #[]
  /--
  Direct and transitive imports. Modules are given with their effective import modifiers, not their
  original ones. Each module is listed at most once. The index of a module in the array equals the
  `ModuleIdx` for the same module.
  -/
  modules      : Array EffectiveImport := #[]
  /--
  Subset of `modules` for which `importAll` is `true`. This is assumed to be a much smaller set so
  we precompute it instead of iterating over all of `modules` multiple times. However, note that
  in a non-`module` file, this is identical to `modules`.
  -/
  importAllModules : Array EffectiveImport := modules.filter (·.importAll)
  /-- Module data for all imported modules. -/
  moduleData   : Array ModuleData := #[]
  deriving Nonempty

/--
Name of all imported modules (directly and indirectly).
The index of a module name in the array equals the `ModuleIdx` for the same module.
-/
def EnvironmentHeader.moduleNames (header : EnvironmentHeader) : Array Name :=
  header.modules.map (·.module)

namespace Kernel

structure Diagnostics where
  /-- Number of times each declaration has been unfolded by the kernel. -/
  unfoldCounter : PHashMap Name Nat := {}
  /-- If `enabled = true`, kernel records declarations that have been unfolded. -/
  enabled : Bool := false
  deriving Inhabited

/--
An environment stores declarations provided by the user. The kernel
currently supports different kinds of declarations such as definitions, theorems,
and inductive families. Each has a unique identifier (i.e., `Name`), and can be
parameterized by a sequence of universe parameters.
A constant in Lean is just a reference to a `ConstantInfo` object. The main task of
the kernel is to type check these declarations and refuse type incorrect ones. The
kernel does not allow declarations containing metavariables and/or free variables
to be added to an environment. Environments are never destructively updated.

The environment also contains a collection of extensions. For example, the `simp` theorems
declared by users are stored in an environment extension. Users can declare new extensions
using meta-programming.
-/
structure Environment where
  /--
  The constructor of `Environment` is private to protect against modification that bypasses the
  kernel.
  -/
  private mk ::
  /--
  Mapping from constant name to `ConstantInfo`. It contains all constants (definitions, theorems,
  axioms, etc) that have been already type checked by the kernel.
  -/
  constants   : ConstMap
  /--
  `quotInit = true` if the command `init_quot` has already been executed for the environment, and
  `Quot` declarations have been added to the environment. When the flag is set, the type checker can
  assume that the `Quot` declarations in the environment have indeed been added by the kernel and
  not by the user.
  -/
  quotInit    : Bool := false
  /--
  Diagnostic information collected during kernel execution.

  Remark: We store kernel diagnostic information in an environment field to simplify the interface
  with the kernel implemented in C/C++. Thus, we can only track declarations in methods, such as
  `addDecl`, which return a new environment. `Kernel.isDefEq` and `Kernel.whnf` do not update the
  statistics. We claim this is ok since these methods are mainly used for debugging.
  -/
  diagnostics : Diagnostics := {}
  /--
  Mapping from constant name to module (index) where constant has been declared.
  Recall that a Lean file has a header where previously compiled modules can be imported.
  Each imported module has a unique `ModuleIdx`.
  Many extensions use the `ModuleIdx` to efficiently retrieve information stored in imported modules.

  Remark: this mapping also contains auxiliary constants, created by the code generator, that are **not** in
  the field `constants`. These auxiliary constants are invisible to the Lean kernel and elaborator.
  Only the code generator uses them.
  -/
  const2ModIdx            : Std.HashMap Name ModuleIdx
  /--
  Environment extensions. It also includes user-defined extensions.
  -/
  private extensions      : Array EnvExtensionState
  /--
  Additional imported environment extension state for the interpreter. Access via
  `getModuleIREntries`.
  -/
  private irBaseExts      : Array EnvExtensionState
  /-- The header contains additional information that is set at import time. -/
  header                  : EnvironmentHeader := {}
deriving Nonempty

/-- Exceptions that can be raised by the kernel when type checking new declarations. -/
inductive Exception where
  | unknownConstant  (env : Environment) (name : Name)
  | alreadyDeclared  (env : Environment) (name : Name)
  | declTypeMismatch (env : Environment) (decl : Declaration) (givenType : Expr)
  | declHasMVars     (env : Environment) (name : Name) (expr : Expr)
  | declHasFVars     (env : Environment) (name : Name) (expr : Expr)
  | funExpected      (env : Environment) (lctx : LocalContext) (expr : Expr)
  | typeExpected     (env : Environment) (lctx : LocalContext) (expr : Expr)
  | letTypeMismatch  (env : Environment) (lctx : LocalContext) (name : Name) (givenType : Expr) (expectedType : Expr)
  | exprTypeMismatch (env : Environment) (lctx : LocalContext) (expr : Expr) (expectedType : Expr)
  | appTypeMismatch  (env : Environment) (lctx : LocalContext) (app : Expr) (funType : Expr) (argType : Expr)
  | invalidProj      (env : Environment) (lctx : LocalContext) (proj : Expr)
  | thmTypeIsNotProp (env : Environment) (name : Name) (type : Expr)
  | other            (msg : String)
  | deterministicTimeout
  | excessiveMemory
  | deepRecursion
  | interrupted
deriving Nonempty

namespace Environment

@[export lean_environment_find]
def find? (env : Environment) (n : Name) : Option ConstantInfo :=
  /- It is safe to use `find'` because we never overwrite imported declarations. -/
  env.constants.find?' n

@[export lean_environment_mark_quot_init]
private def markQuotInit (env : Environment) : Environment :=
  { env with quotInit := true }

@[export lean_environment_quot_init]
private def isQuotInit (env : Environment) : Bool :=
  env.quotInit

/-- Type check given declaration and add it to the environment -/
@[extern "lean_add_decl"]
opaque addDeclCore (env : Environment) (maxHeartbeats : USize) (decl : @& Declaration)
  (cancelTk? : @& Option IO.CancelToken) : Except Exception Environment

/--
Add declaration to kernel without type checking it.

**WARNING** This function is meant for temporarily working around kernel performance issues.
It compromises soundness because, for example, a buggy tactic may produce an invalid proof,
and the kernel will not catch it if the new option is set to true.
-/
@[extern "lean_add_decl_without_checking"]
opaque addDeclWithoutChecking (env : Environment) (decl : @& Declaration) : Except Exception Environment

@[export lean_environment_add]
private def add (env : Environment) (cinfo : ConstantInfo) : Environment :=
  { env with constants := env.constants.insert cinfo.name cinfo }

@[export lean_kernel_diag_is_enabled]
def Diagnostics.isEnabled (d : Diagnostics) : Bool :=
  d.enabled

/-- Enables/disables kernel diagnostics. -/
def enableDiag (env : Environment) (flag : Bool) : Environment :=
  { env with diagnostics.enabled := flag }

def isDiagnosticsEnabled (env : Environment) : Bool :=
  env.diagnostics.enabled

def resetDiag (env : Environment) : Environment :=
  { env with diagnostics.unfoldCounter := {} }

@[export lean_kernel_record_unfold]
def Diagnostics.recordUnfold (d : Diagnostics) (declName : Name) : Diagnostics :=
  if d.enabled then
    let cNew := if let some c := d.unfoldCounter.find? declName then c + 1 else 1
    { d with unfoldCounter := d.unfoldCounter.insert declName cNew }
  else
    d

@[export lean_kernel_get_diag]
def getDiagnostics (env : Environment) : Diagnostics :=
  env.diagnostics

@[export lean_kernel_set_diag]
def setDiagnostics (env : Environment) (diag : Diagnostics) : Environment :=
  { env with diagnostics := diag}

end Kernel.Environment



inductive ConstantKind where
  | defn | thm | «axiom» | «opaque» | quot | induct | ctor | recursor
deriving Inhabited, BEq, Repr

def ConstantKind.ofConstantInfo : ConstantInfo → ConstantKind
  | .defnInfo   _ => .defn
  | .thmInfo    _ => .thm
  | .axiomInfo  _ => .axiom
  | .opaqueInfo _ => .opaque
  | .quotInfo   _ => .quot
  | .inductInfo _ => .induct
  | .ctorInfo   _ => .ctor
  | .recInfo    _ => .recursor

/-- `ConstantInfo` variant that allows for asynchronous filling of components via tasks. -/
structure AsyncConstantInfo where
  /-- The declaration name, known immediately. -/
  name      : Name
  /-- The kind of the constant, known immediately. -/
  kind      : ConstantKind
  /-- The "signature" including level params and type, potentially filled asynchronously. -/
  sig       : Task ConstantVal
  /-- The final, complete constant info, potentially filled asynchronously. -/
  constInfo : Task ConstantInfo
deriving Inhabited

namespace AsyncConstantInfo

def toConstantVal (c : AsyncConstantInfo) : ConstantVal :=
  c.sig.get

def toConstantInfo (c : AsyncConstantInfo) : ConstantInfo :=
  c.constInfo.get

def ofConstantInfo (c : ConstantInfo) : AsyncConstantInfo where
  name := c.name
  kind := .ofConstantInfo c
  sig := .pure c.toConstantVal
  constInfo := .pure c

def isUnsafe (c : AsyncConstantInfo) : Bool :=
  match c.kind with
  | .thm => false
  | _ => c.toConstantInfo.isUnsafe

end AsyncConstantInfo

/--
Information about the current branch of the environment representing asynchronous elaboration.

Use `Environment.enterAsync` instead of `mkRaw`.
-/
private structure AsyncContext where mkRaw ::
  /--
  Name of the declaration asynchronous elaboration was started for. All constants added to this
  environment branch must have the name as a prefix, after erasing macro scopes and private name
  prefixes.
  -/
  declPrefix : Name
  /--
  Reverse list of ongoing `realizeConst` calls, used to restrict env ext modifications and detect
  cyclic realizations.
  -/
  realizingStack : List Name
deriving Nonempty

/--
Checks whether a declaration named `n` may be added to the environment in the given context. See
also `AsyncContext.declPrefix`.
-/
private def AsyncContext.mayContain (ctx : AsyncContext) (n : Name) : Bool :=
  ctx.declPrefix.isPrefixOf <| privateToUserName n.eraseMacroScopes

/--
Constant info and environment extension states eventually resulting from async elaboration.
-/
private structure AsyncConst where
  constInfo   : AsyncConstantInfo
  /--
  Reported extension state eventually fulfilled by promise; may be missing for tasks (e.g. kernel
  checking) that can eagerly guarantee they will not report any state.
  -/
  exts?       : Option (Task (Array EnvExtensionState))
  /--
  `Task AsyncConsts` except for problematic recursion. The set of nested constants created while
  elaborating this constant.
  -/
  aconstsImpl : Task Dynamic
  /-- True if generated by `realizeConst`. -/
  isRealized  : Bool := false

/-- Data structure holding a sequence of `AsyncConst`s optimized for efficient access. -/
private structure AsyncConsts where
  size : Nat
  revList : List AsyncConst
  /-- Map from declaration name to const for fast direct access. -/
  map : NameMap AsyncConst
  /-- Trie of declaration names without private name prefixes for fast longest-prefix access. -/
  normalizedTrie : NameTrie AsyncConst
deriving Inhabited, TypeName

private def AsyncConst.aconsts (c : AsyncConst) : Task AsyncConsts :=
  c.aconstsImpl.map (sync := true) fun dyn =>
    dyn.get? AsyncConsts |>.getD default

private def AsyncConsts.add (aconsts : AsyncConsts) (aconst : AsyncConst) : AsyncConsts :=
  let normalizedName := privateToUserName aconst.constInfo.name
  if let some aconst' := aconsts.normalizedTrie.find? normalizedName then
    let _ : Inhabited AsyncConsts := ⟨aconsts⟩
    panic! s!"duplicate normalized declaration name {aconst.constInfo.name} vs. {aconst'.constInfo.name}"
  else { aconsts with
    size := aconsts.size + 1
    revList := aconst :: aconsts.revList
    map := aconsts.map.insert aconst.constInfo.name aconst
    normalizedTrie := aconsts.normalizedTrie.insert normalizedName aconst
  }

private def AsyncConsts.find? (aconsts : AsyncConsts) (declName : Name) : Option AsyncConst :=
  aconsts.map.find? declName

/-- Finds the constant in the collection that is a prefix of `declName`, if any. -/
private def AsyncConsts.findPrefix? (aconsts : AsyncConsts) (declName : Name) : Option AsyncConst :=
  -- as macro scopes are a strict suffix, we do not have to remove them before calling
  -- `findLongestPrefix?`
  aconsts.normalizedTrie.findLongestPrefix? (privateToUserName declName)

/--
Finds constants including from other environment branches by recursively looking up longest
prefixes (which is sufficient by `AsyncContext.mayContain`).
-/
private partial def AsyncConsts.findRec? (aconsts : AsyncConsts) (declName : Name) : Option AsyncConst := do
  let c ← aconsts.findPrefix? declName
  if c.constInfo.name == declName then
    return c
  -- If privacy is the only difference between `declName` and `findPrefix?` result, we can assume
  -- `declName` does not exist according to the `add` invariant
  guard <| privateToUserName c.constInfo.name != privateToUserName declName
  let aconsts ← c.aconsts.get
  AsyncConsts.findRec? aconsts declName

/-- Like `findRec?`; allocating tasks is (currently?) too costly to do always. -/
private partial def AsyncConsts.findRecTask (aconsts : AsyncConsts) (declName : Name) : Task (Option AsyncConst) := Id.run do
  let some c := aconsts.findPrefix? declName | .pure none
  if c.constInfo.name == declName then
    return .pure c
  c.aconsts.bind (sync := true) fun aconsts => Id.run do
    AsyncConsts.findRecTask aconsts declName

/-- Like `findRec?` but also returns the constant that has `declName` in its `consts`, if any. -/
private partial def AsyncConsts.findRecAndParent? (aconsts : AsyncConsts) (declName : Name) : Option (AsyncConst × Option AsyncConst) :=
  go none aconsts
where go parent? aconsts := do
  let c ← aconsts.findPrefix? declName
  if c.constInfo.name == declName then
    return (c, parent?)
  -- If privacy is the only difference between `declName` and `findPrefix?` result, we can assume
  -- `declName` does not exist according to the `add` invariant
  guard <| privateToUserName c.constInfo.name != privateToUserName declName
  go (some c) c.aconsts.get

/-- Accessibility levels of declarations in `Lean.Environment`. -/
private inductive Visibility where
  /-- Information private to the module. -/
  | «private»
  /-- Information to be exported to other modules. -/
  | «public»

/-- Maps `Visibility` to `α`. -/
private structure VisibilityMap (α : Type) where
  «private» : α
  «public»  : α
deriving Inhabited, Nonempty

/-- Context for `realizeConst` established by `enableRealizationsForConst`. -/
private structure RealizationContext where
  /--
  Saved `Environment`, untyped to avoid cyclic reference. Import environment for imported constants.
  -/
  env       : NonScalar
  /-- Saved options. Empty for imported constants. -/
  opts      : Options
  /--
  `realizeValue _ key ..` adds a mapping from `(typeName key, key)` to a task of the realization
  result (`RealizeValueResult` when called from `Lean.realizeValue`, `RealizeConstResult` from
  `Environment.realizeConst`).
  -/
  realizeMapRef : IO.Ref (NameMap NonScalar /- PHashMap α (Task Dynamic) -/)

/--
Elaboration-specific extension of `Kernel.Environment` that adds tracking of asynchronously
elaborated declarations.
-/
structure Environment where
  /-
  Like with `Kernel.Environment`, this constructor is private to protect consistency of the
  environment, though there are no soundness concerns in this case given that it is used purely for
  elaboration.
  -/
  private mk ::
  /--
  Kernel environments containing imported constants. Also stores environment extension state for the
  current branch of the environment (in `private`). Any other data should be considered
  indeterminate.

  As `base` is eagerly available, we prefer taking information from it instead of `checked` whenever
  possible.
  -/
  private base : VisibilityMap Kernel.Environment
  /--
  Additional imported environment extension state for use in the language server. This field is
  identical to `base.extensions` in other contexts. Access via
  `getModuleEntries (level := .server)`.
  -/
  private serverBaseExts : Array EnvExtensionState := private_decl% base.private.extensions
  /--
  Kernel environment task that is fulfilled when all asynchronously elaborated declarations are
  finished, containing the resulting environment. Also collects the environment extension state of
  all environment branches that contributed contained declarations.
  -/
  checked             : Task Kernel.Environment := private_decl% (.pure base.private)
  /--
  Container of asynchronously elaborated declarations. For consistency, `Lean.addDecl` makes sure
  this contains constants added even synchronously, i.e. `base ⨃ asyncConsts` is the set of
  constants known on the current environment branch, which is a subset of `checked`.

  Private view should correspond to kernel map. Public view may contain fewer constants and less
  data per constant.
  -/
  private asyncConstsMap : VisibilityMap AsyncConsts := default
  /-- Information about this asynchronous branch of the environment, if any. -/
  private asyncCtx?   : Option AsyncContext := none
  /--
  Realized values belonging to imported declarations. Must be initialized by calling
  `enableRealizationsForImports`.
  -/
  private importRealizationCtx? : Option RealizationContext
  /--
  Realized values belonging to local declarations. This is a map from local declarations, which
  need to be registered synchronously using `enableRealizationsForConst`, to their realization
  context.
  -/
  private localRealizationCtxMap  : NameMap RealizationContext := {}
  /--
  Task collecting all realized constants from the current and already-forked environment branches,
  akin to how `checked` collects all declarations. We only use it as a fallback in
  `findAsyncCore?`/`getState`; see there.
  -/
  private allRealizations : Task (NameMap AsyncConst) := .pure {}
  /--
  Indicates whether the environment is being used in an exported context, i.e. whether it should
  provide access to only the data to be imported by other modules participating in the module
  system.
  -/
  isExporting : Bool := false
deriving Nonempty

@[inline] private def VisibilityMap.get (m : VisibilityMap α) (env : Environment) : α :=
  if env.isExporting then m.public else m.private

private def VisibilityMap.map (m : VisibilityMap α) (f : α → β) : VisibilityMap β where
  «private» := f m.private
  «public»  := f m.public

private def VisibilityMap.const (a : α) : VisibilityMap α :=
  { «private» := a, «public» := a }

namespace Environment

def header (env : Environment) : EnvironmentHeader :=
  -- can be assumed to be in sync with `env.checked`; see `setMainModule`, the only modifier of the header
  env.base.private.header

def imports (env : Environment) : Array Import :=
  env.header.imports

def allImportedModuleNames (env : Environment) : Array Name :=
  env.header.moduleNames

private def asyncConsts (env : Environment) : AsyncConsts :=
  env.asyncConstsMap.get env

-- Used only when the kernel calls into the interpreter, and in `Lean.Kernel.Exception.mkCtx`. In
-- both cases, the environment should be temporary and not leak into elaboration.
@[export lean_elab_environment_of_kernel_env]
def ofKernelEnv (env : Kernel.Environment) : Environment :=
  { base.private := env, base.public := env, importRealizationCtx? := none }

@[export lean_elab_environment_to_kernel_env]
def toKernelEnv (env : Environment) : Kernel.Environment :=
  env.checked.get

/-- Updates `env.isExporting`. Ignored if `env.header.isModule` is false. -/
def setExporting (env : Environment) (isExporting : Bool) : Environment :=
  if !env.header.isModule || env.isExporting == isExporting then
    env
  else
    { env with isExporting }

/-- Consistently updates synchronous and (private) asynchronous parts of the environment without blocking. -/
private def modifyCheckedAsync (env : Environment) (f : Kernel.Environment → Kernel.Environment) : Environment :=
  { env with checked := env.checked.map (sync := true) f, base.private := f env.base.private }

/-- Sets synchronous and (private) asynchronous parts of the environment to the given kernel environment. -/
private def setCheckedSync (env : Environment) (newChecked : Kernel.Environment) : Environment :=
  { env with checked := .pure newChecked, base.private := newChecked }

/-- The declaration prefix to which the environment is restricted to, if any. -/
def asyncPrefix? (env : Environment) : Option Name :=
  env.asyncCtx?.map (·.declPrefix)

/-- True while inside `realizeConst`'s `realize`. -/
def isRealizing (env : Environment) : Bool :=
  env.asyncCtx?.any (!·.realizingStack.isEmpty)

/--
Returns the environment just after importing. `none` if `finalizeImport` has never been called on
it.
-/
def importEnv? (env : Environment) : Option Environment :=
  -- safety: `RealizationContext` is private
  unsafe env.importRealizationCtx?.map (unsafeCast (β := Environment) ·.env)

/-- Forgets about the asynchronous context restrictions. Used only for `withoutModifyingEnv`. -/
def unlockAsync (env : Environment) : Environment :=
  { env with asyncCtx? := none }

@[extern "lean_elab_add_decl"]
private opaque addDeclCheck (env : Environment) (maxHeartbeats : USize) (decl : @& Declaration)
  (cancelTk? : @& Option IO.CancelToken) : Except Kernel.Exception Environment

@[extern "lean_elab_add_decl_without_checking"]
private opaque addDeclWithoutChecking (env : Environment) (decl : @& Declaration) :
  Except Kernel.Exception Environment

/--
Adds given declaration to the environment, type checking it unless `doCheck` is false.

This is a plumbing function for the implementation of `Lean.addDecl`, most users should use it
instead.
-/
def addDeclCore (env : Environment) (maxHeartbeats : USize) (decl : @& Declaration)
    (cancelTk? : @& Option IO.CancelToken) (doCheck := true) :
    Except Kernel.Exception Environment := do
  if let some ctx := env.asyncCtx? then
    if let some n := decl.getTopLevelNames.find? (!ctx.mayContain ·) then
      throw <| .other s!"cannot add declaration {n} to environment as it is restricted to the \
        prefix {ctx.declPrefix}"
  let mut env ← if doCheck then
    addDeclCheck env maxHeartbeats decl cancelTk?
  else
    addDeclWithoutChecking env decl

  -- Let the elaborator know about the new constants. This uses the same constant for both
  -- visibility scopes but the caller can still customize the public one on the main elaboration
  -- branch by use of `addConstAsync` as is the case for `Lean.addDecl`.
  for n in decl.getNames do
    let some info := env.checked.get.find? n | unreachable!
    env := { env with asyncConstsMap.private := env.asyncConstsMap.private.add {
      constInfo := .ofConstantInfo info
      exts? := none
      aconstsImpl := .pure <| .mk (α := AsyncConsts) default
    } }
    -- TODO
    if true /- !isPrivateName n-/ then
      env := { env with asyncConstsMap.public := env.asyncConstsMap.public.add {
        constInfo := .ofConstantInfo info
        exts? := none
        aconstsImpl := .pure <| .mk (α := AsyncConsts) default
      } }

  return env

@[inherit_doc Kernel.Environment.constants]
def constants (env : Environment) : ConstMap :=
  env.toKernelEnv.constants

@[inherit_doc Kernel.Environment.const2ModIdx]
def const2ModIdx (env : Environment) : Std.HashMap Name ModuleIdx :=
  env.toKernelEnv.const2ModIdx

-- only needed for the lakefile.lean cache
@[export lake_environment_add]
private def lakeAdd (env : Environment) (cinfo : ConstantInfo) : Environment :=
  let env := env.setCheckedSync <| env.checked.get.add cinfo
  {
    env with
    asyncConstsMap := env.asyncConstsMap.map (·.add {
      constInfo := .ofConstantInfo cinfo
      exts? := none
      aconstsImpl := .pure <| .mk (α := AsyncConsts) default
    })
  }

-- forward reference due to too many cyclic dependencies
@[extern "lean_is_reserved_name"]
private opaque isReservedName (env : Environment) (name : Name) : Bool

@[inline] private def findAsyncConst? (env : Environment) (n : Name) (skipRealize := false) :
    Option AsyncConst := do
  if let some c := env.asyncConsts.find? n then
    -- Constant for which an asynchronous elaboration task was spawned
    -- (this is an optimized special case of the next branch)
    return c
  if let some c := env.asyncConsts.findRec? n then
    -- Constant generated in a different environment branch
    return c
  if !skipRealize && isReservedName env n then
    if let some c := env.allRealizations.get.find? n then
      return c
  -- Not in the kernel environment nor in the name prefix of a known environment branch: undefined
  -- by `addDeclCore` invariant.
  none

/-- `findAsync?` after `base` access -/
private def findAsyncCore? (env : Environment) (n : Name) (skipRealize := false) :
    Option AsyncConstantInfo := do
  env.findAsyncConst? n (skipRealize := skipRealize) |>.map (·.constInfo)

/-- Like `findAsyncCore?`; allocating tasks is (currently?) too costly to do always. -/
private def findTaskCore (env : Environment) (n : Name) (skipRealize := false) :
    Task (Option AsyncConstantInfo) := Id.run do
  if let some c := env.asyncConsts.find? n then
    -- Constant for which an asynchronous elaboration task was spawned
    -- (this is an optimized special case of the next branch)
    return .pure c.constInfo
  env.asyncConsts.findRecTask n |>.bind (sync := true) fun
  | some c =>
    -- Constant generated in a different environment branch
    .pure c.constInfo
  | _ => Id.run do
    if isReservedName env n && !skipRealize then
      return env.allRealizations.map (sync := true) fun allRealizations => do
        if let some c := allRealizations.find? n then
          return c.constInfo
        none
    -- Not in the kernel environment nor in the name prefix of a known environment branch: undefined
    -- by `addDeclCore` invariant.
    .pure none

/--
Looks up the given declaration name in the environment, avoiding forcing any in-progress elaboration
tasks unless necessary. This can usually be done efficiently because `addConstAsync` ensures that
declarations added in an environment branch have that branch's declaration name as a prefix, so we
know exactly what tasks to wait for to find a declaration. However, this is not true for
declarations from `realizeConst`, which are not restricted to the current prefix, and reference to
which may escape the branch(es) they have been realized on such as when looking into the type `Expr`
of a declaration found on another branch. Thus when we cannot find the declaration using the fast
prefix-based lookup, we fall back to waiting for and looking at the realizations from all branches.
To avoid this expensive search for realizations from other branches, `skipRealize` can be set to ensure
negative lookups are as fast as positive ones.

Use `findTask` instead if any blocking should be avoided.
-/
def findAsync? (env : Environment) (n : Name) (skipRealize := false) : Option AsyncConstantInfo := do
  -- Avoid going through `AsyncConstantInfo` for `base` access
  if let some c := env.base.get env |>.constants.map₁[n]? then
    return .ofConstantInfo c
  findAsyncCore? (skipRealize := skipRealize) env n

/-- Like `findAsync?` but returns a task instead of resorting to blocking. -/
def findTask (env : Environment) (n : Name) (skipRealize := false) : Task (Option AsyncConstantInfo) := Id.run do
  -- Avoid going through `AsyncConstantInfo` for `base` access
  if let some c := env.base.get env |>.constants.map₁[n]? then
    return .pure <| some <| .ofConstantInfo c
  findTaskCore (skipRealize := skipRealize) env n

/--
Like `findAsync` but blocks on everything but the constant's body (if any), which is not accessible
through the result.
-/
def findConstVal? (env : Environment) (n : Name) (skipRealize := false) : Option ConstantVal := do
  -- Avoid going through `AsyncConstantInfo` for `base` access
  if let some c := env.base.get env |>.constants.map₁[n]? then
    return c.toConstantVal
  env.findAsyncCore? n (skipRealize := skipRealize) |>.map (·.toConstantVal)

/-- Like `findAsync?`, but blocks until the constant's info is fully available.  -/
def find? (env : Environment) (n : Name) (skipRealize := false) : Option ConstantInfo := do
  if let some c := env.base.get env |>.constants.map₁[n]? then
    return c
  env.findAsyncCore? n (skipRealize := skipRealize) |>.map (·.toConstantInfo)

/--
Allows `realizeConst` calls for the given declaration in all derived environment branches.
Realizations will run using the given environment and options to ensure deterministic results. Note
that while we check that the function isn't called before the declaration is actually added to the
environment, we cannot automatically check that it isn't otherwise called too early in the sense
that helper declarations and environment extension state that may be relevant to realizations may
not have been added yet. We do check that we are not calling it from a different branch than `c` was
added on, which would be definitely too late. Thus, this function should generally be called in
elaborators calling `addDecl` (when that declaration is a plausible target for realization) at the
latest possible point, i.e. at the very end of the elaborator or just before a first realization may
be triggered if any.
-/
def enableRealizationsForConst (env : Environment) (opts : Options) (c : Name) :
    BaseIO Environment := do
  -- Meta code working on a non-exported declaration should usually do so inside `withoutExporting`
  -- but we're lenient here in case this call is the only one that needs the setting.
  if env.setExporting false |>.findAsync? c |>.isNone then
    panic! s!"declaration {c} not found in environment"
    return env
  if let some asyncCtx := env.asyncCtx? then
    if !asyncCtx.mayContain c then
      panic! s!"{c} is outside current context {asyncCtx.declPrefix}"
      return env
  if env.localRealizationCtxMap.contains c then
    return env
  return { env with localRealizationCtxMap := env.localRealizationCtxMap.insert c {
    -- safety: `RealizationContext` is private
    env := unsafe unsafeCast env
    opts
    realizeMapRef := (← IO.mkRef {}) } }

def areRealizationsEnabledForConst (env : Environment) (c : Name) : Bool :=
  (env.base.get env |>.const2ModIdx.contains c) || env.localRealizationCtxMap.contains c

/-- Returns debug output about the asynchronous state of the environment. -/
def dbgFormatAsyncState (env : Environment) : BaseIO String :=
  return s!"\
    asyncCtx.declPrefix: {repr <| env.asyncCtx?.map (·.declPrefix)}\
  \nasyncConsts: {repr <| env.asyncConsts.revList.reverse.map (·.constInfo.name)}
  \nbase.private.constants.map₂: {repr <| env.base.private.constants.map₂.toList.map (·.1)}"

/-- Returns debug output about the synchronous state of the environment. -/
def dbgFormatCheckedSyncState (env : Environment) : BaseIO String :=
  return s!"checked.get.constants.map₂: {repr <| env.checked.get.constants.map₂.toList.map (·.1)}"

/-- Result of `Lean.Environment.promiseChecked`. -/
structure PromiseCheckedResult where
  /--
  Resulting "main branch" environment. Accessing the kernel environment will block until
  `PromiseCheckedResult.commitChecked` has been called.
  -/
  mainEnv : Environment
  /--
  Resulting "async branch" environment which should be used in a new task and then to call
  `PromiseCheckedResult.commitChecked` to commit results back to the main environment. If it is not
  called and the `PromiseCheckedResult` object is dropped, the kernel environment will be left
  unchanged.
  -/
  asyncEnv : Environment
  private checkedEnvPromise : IO.Promise Kernel.Environment

def realizingStack (env : Environment) : List Name :=
  env.asyncCtx?.map (·.realizingStack) |>.getD []

/-- Creates an async context for the given declaration name, normalizing it for use as a prefix. -/
private def enterAsync (declName : Name) (env : Environment) : Environment :=
  { env with asyncCtx? := some {
    declPrefix := privateToUserName declName.eraseMacroScopes
    realizingStack := env.realizingStack } }

/-- Creates an async context when realizing `declName` -/
private def enterAsyncRealizing (declName : Name) (env : Environment) : Environment :=
  { env with asyncCtx? := some {
    declPrefix := .anonymous
    realizingStack := declName :: env.realizingStack } }

/--
Starts an asynchronous modification of the kernel environment. The environment is split into a
"main" branch that will block on access to the kernel environment until
`PromiseCheckedResult.commitChecked` has been called on the "async" environment branch.
-/
def promiseChecked (env : Environment) : BaseIO PromiseCheckedResult := do
  let checkedEnvPromise ← IO.Promise.new
  return {
    mainEnv := { env with
      checked := checkedEnvPromise.result?.bind (sync := true) fun
        | some kenv => .pure kenv
        | none      => env.checked }
    -- Do not allow adding new constants
    asyncEnv := env.enterAsync `__reserved__Environment_promiseChecked
    checkedEnvPromise
  }

/-- Commits the kernel environment of the given environment back to the main branch. -/
def PromiseCheckedResult.commitChecked (res : PromiseCheckedResult) (env : Environment) :
    BaseIO Unit :=
  assert! env.asyncCtx?.isSome
  res.checkedEnvPromise.resolve env.toKernelEnv

/-- Data transmitted by `AddConstAsyncResult.commitConst`. -/
private structure ConstPromiseVal where
  privateConstInfo     : ConstantInfo
  exportedConstInfo    : ConstantInfo
  exts                 : Array EnvExtensionState
  nestedConsts         : VisibilityMap AsyncConsts
deriving Nonempty

/--
Result of `Lean.Environment.addConstAsync` which is necessary to complete the asynchronous addition.
-/
structure AddConstAsyncResult where
  /--
  Resulting "main branch" environment which contains the declaration name as an asynchronous
  constant. Accessing the constant or kernel environment will block until the corresponding
  `AddConstAsyncResult.commit*` function has been called.
  -/
  mainEnv : Environment
  /--
  Resulting "async branch" environment which should be used to add the desired declaration in a new
  task and then call `AddConstAsyncResult.commit*` to commit results back to the main environment.
  `commitCheckEnv` completes the addition; if it is not called and the `AddConstAsyncResult` object
  is dropped, `sorry`ed default values will be reported instead and the kernel environment will be
  left unchanged.
  -/
  asyncEnv : Environment
  private constName : Name
  private kind : ConstantKind
  private exportedKind? : Option ConstantKind
  private sigPromise : IO.Promise ConstantVal
  private constPromise : IO.Promise ConstPromiseVal
  private checkedEnvPromise : IO.Promise Kernel.Environment
  private allRealizationsPromise : IO.Promise (NameMap AsyncConst)

/-- Creates fallback info to be used in case promises are dropped unfulfilled. -/
private def mkFallbackConstInfo (constName : Name) (kind : ConstantKind) : ConstantInfo :=
  let fallbackVal : ConstantVal := {
    name := constName
    levelParams := []
    type := mkApp2 (mkConst ``sorryAx [1]) (mkSort 0) (mkConst ``true)
  }
  match kind with
    | .defn => .defnInfo { fallbackVal with
      value := mkApp2 (mkConst ``sorryAx [0]) fallbackVal.type (mkConst ``true)
      hints := .abbrev
      safety := .safe
    }
    | .thm  => .thmInfo { fallbackVal with
      value := mkApp2 (mkConst ``sorryAx [0]) fallbackVal.type (mkConst ``true)
    }
    | .axiom  => .axiomInfo { fallbackVal with
      isUnsafe := false
    }
    | k => panic! s!"unsupported constant kind {repr k}"

/--
Starts the asynchronous addition of a constant to the environment. The environment is split into a
"main" branch that holds a reference to the constant to be added but will block on access until the
corresponding information has been added on the "async" environment branch and committed there; see
the respective fields of `AddConstAsyncResult` as well as the [Environment Branches] note for more
information.

`exportedKind?` must be passed if the eventual kind of the constant in the exported constant map
will differ from that of the private version. It must be `none` if the constant will not be
exported.
-/
def addConstAsync (env : Environment) (constName : Name) (kind : ConstantKind)
    (exportedKind? : Option ConstantKind := some kind) (reportExts := true) (checkMayContain := true) :
    IO AddConstAsyncResult := do
  if checkMayContain then
    if let some ctx := env.asyncCtx? then
      if !ctx.mayContain constName then
        throw <| .userError s!"cannot add declaration {constName} to environment as it is \
          restricted to the prefix {ctx.declPrefix}"
  let sigPromise ← IO.Promise.new
  let constPromise ← IO.Promise.new
  let allRealizationsPromise ← IO.Promise.new
  let checkedEnvPromise ← IO.Promise.new

  let privateAsyncConst := {
    constInfo := {
      name := constName
      kind
      sig := sigPromise.resultD (mkFallbackConstInfo constName kind).toConstantVal
      constInfo := constPromise.result?.map (sync := true) fun
        | some c => c.privateConstInfo
        | none   => mkFallbackConstInfo constName kind
    }
    exts? := guard reportExts *> some (constPromise.result?.map (sync := true) fun
      | some v => v.exts
      -- any value should work here, `base` does not block
      | none   => env.base.private.extensions)
    aconstsImpl := constPromise.result?.map (sync := true) fun
      | some v => .mk v.nestedConsts.private
      | none   => .mk (α := AsyncConsts) default
  }
  let exportedAsyncConst? := exportedKind?.map fun exportedKind => { privateAsyncConst with
    constInfo := { privateAsyncConst.constInfo with
      kind := exportedKind
      constInfo := constPromise.result?.map (sync := true) fun
        | some c => c.exportedConstInfo
        | none   => mkFallbackConstInfo constName exportedKind
    }
    aconstsImpl := constPromise.result?.map (sync := true) fun
      | some v => .mk v.nestedConsts.public
      | none   => .mk (α := AsyncConsts) default
  }
  return {
    constName, kind, exportedKind?
    mainEnv := { env with
      asyncConstsMap := {
        «private» := env.asyncConstsMap.private.add privateAsyncConst
        «public»  := exportedAsyncConst?.map (env.asyncConstsMap.public.add ·)
          |>.getD env.asyncConstsMap.public
      }
      checked := checkedEnvPromise.result?.bind (sync := true) fun
        | some kenv => .pure kenv
        | none      => env.checked
      allRealizations := allRealizationsPromise.result?.bind (sync := true) fun
        | some r => .pure r
        | none   => env.allRealizations }
    asyncEnv := env.enterAsync constName
    sigPromise, constPromise, allRealizationsPromise, checkedEnvPromise
  }

/--
Commits the signature of the constant to the main environment branch. The declaration name must
match the name originally given to `addConstAsync`. It is optional to call this function but can
help in unblocking corresponding accesses to the constant on the main branch.
-/
def AddConstAsyncResult.commitSignature (res : AddConstAsyncResult) (sig : ConstantVal) :
    IO Unit := do
  if sig.name != res.constName then
    throw <| .userError s!"AddConstAsyncResult.commitSignature: constant has name {sig.name} but expected {res.constName}"
  res.sigPromise.resolve sig

/--
Commits the full constant info as well as the current environment extension state and set of nested
asynchronous constants to the main environment branch. If `info?` is `none`, it is taken from the
given environment. The declaration name and kind must match the original values given to
`addConstAsync`. The signature must match the previous `commitSignature` call, if any.
-/
def AddConstAsyncResult.commitConst (res : AddConstAsyncResult) (env : Environment)
    (info? : Option ConstantInfo := none) (exportedInfo? : Option ConstantInfo := none) :
    IO Unit := do
  -- Make sure to access the non-exported version here
  let info ← match info? <|> (env.setExporting false).find? res.constName with
    | some info => pure info
    | none =>
      throw <| .userError s!"AddConstAsyncResult.commitConst: constant {res.constName} not found in async context"
  res.commitSignature info.toConstantVal
  let kind' := .ofConstantInfo info
  if res.kind != kind' then
    throw <| .userError s!"AddConstAsyncResult.commitConst: constant has kind {repr kind'} but expected {repr res.kind}"
  let sig := res.sigPromise.result!.get
  if sig.levelParams != info.levelParams then
    throw <| .userError s!"AddConstAsyncResult.commitConst: constant has level params {info.levelParams} but expected {sig.levelParams}"
  if sig.type != info.type then
    throw <| .userError s!"AddConstAsyncResult.commitConst: constant has type {info.type} but expected {sig.type}"
  let mut exportedInfo? := exportedInfo?
  if let some exportedInfo := exportedInfo? then
    if exportedInfo.toConstantVal != info.toConstantVal then
      -- may want to add more details if necessary
      throw <| .userError s!"AddConstAsyncResult.commitConst: exported constant has different signature"
  else if res.exportedKind?.isNone then
    exportedInfo? := some info  -- avoid `find?` call, ultimately unused
  res.constPromise.resolve {
    privateConstInfo := info
    exportedConstInfo := (exportedInfo? <|> (env.setExporting true).find? res.constName).getD info
    exts := env.base.private.extensions
    nestedConsts := env.asyncConstsMap
  }

/--
Assuming `Lean.addDecl` has been run for the constant to be added on the async environment branch,
commits the full constant info from that call to the main environment, (asynchronously) waits for
the final kernel environment resulting from the `addDecl` call, and commits it to the main branch as
well, unblocking kernel additions there. All `commitConst` preconditions apply.
-/
def AddConstAsyncResult.commitCheckEnv (res : AddConstAsyncResult) (env : Environment) :
    IO Unit := do
  -- We should skip `commitConst` in case it has already been called, perhaps with a different
  -- `info?`
  if !(← res.constPromise.isResolved) then
    res.commitConst env
  BaseIO.chainTask (sync := true) env.checked fun checked => do
    res.checkedEnvPromise.resolve checked
    BaseIO.chainTask (sync := true) env.allRealizations res.allRealizationsPromise.resolve

/--
Checks whether `findAsync?` would return a result.

NOTE: Unlike `findAsync`, this function defaults `skipRealize` to `true` to avoid unnecessary
blocking on realizations, which should always be brought into scope by running `realizeConst`, which
does its own, optimized existence check.
-/
def contains (env : Environment) (n : Name) (skipRealize := true) : Bool :=
  env.findAsync? (skipRealize := skipRealize) n |>.isSome

/--
Checks whether the given declaration is known on the current branch, in which case `findAsync?` will
not block.
-/
def containsOnBranch (env : Environment) (n : Name) : Bool :=
  (env.asyncConsts.find? n |>.isSome) || (env.base.get env).constants.contains n

def setMainModule (env : Environment) (m : Name) : Environment := Id.run do
  let env := env.modifyCheckedAsync ({ · with
    header.mainModule := m
  })
  { env with importRealizationCtx? := env.importRealizationCtx?.map ({ · with
      -- safety: `RealizationContext` is private
      env := unsafe unsafeCast env
    }) }

def mainModule (env : Environment) : Name :=
  env.header.mainModule

def getModuleIdxFor? (env : Environment) (declName : Name) : Option ModuleIdx :=
  -- async constants are always from the current module
  env.base.get env |>.const2ModIdx[declName]?

def isImportedConst (env : Environment) (declName : Name) : Bool :=
  env.getModuleIdxFor? declName |>.isSome

def isConstructor (env : Environment) (declName : Name) : Bool :=
  env.findAsync? declName |>.any (·.kind == .ctor)

def isSafeDefinition (env : Environment) (declName : Name) : Bool :=
  match env.findAsync? declName with
  | some { kind := .defn, constInfo, .. } => (constInfo.get matches .defnInfo { safety := .safe, .. })
  | _ => false

def getModuleIdx? (env : Environment) (moduleName : Name) : Option ModuleIdx :=
  env.header.modules.findIdx? (·.module == moduleName)

end Environment

def ConstantVal.instantiateTypeLevelParams (c : ConstantVal) (ls : List Level) : Expr :=
  c.type.instantiateLevelParams c.levelParams ls

namespace ConstantInfo

def instantiateTypeLevelParams (c : ConstantInfo) (ls : List Level) : Expr :=
  c.toConstantVal.instantiateTypeLevelParams ls

def instantiateValueLevelParams! (c : ConstantInfo) (ls : List Level) : Expr :=
  c.value!.instantiateLevelParams c.levelParams ls

end ConstantInfo

/--
Branch specification for asynchronous environment extension access.

Note: For declarations not created via `addConstAsync`, including those created via `realizeConst`,
the two specifiers are equivalent.
-/
inductive AsyncBranch where
  /--
  The main branch that initiated adding a declaration, i.e. `AddConstAsyncResult.mainEnv`.

  This is the more common case and true for e.g. all accesses from attributes.
  -/
  | mainEnv
  /-- The async branch that finished adding a declaration, i.e. `AddConstAsyncResult.asyncEnv`. -/
  | asyncEnv
deriving BEq

/--
Async access mode for environment extensions used in `EnvExtension.get/set/modifyState`.
When modified in concurrent contexts, extensions may need to switch to a different mode than the
default `mainOnly`, which will panic in such cases. The access mode is set at environment extension
registration time but can be overridden when calling the mentioned functions in order to weaken it
for specific accesses.

In all modes, the state stored into the `.olean` file for persistent environment extensions is the
result of `getState (asyncMode := .sync)` called on the main environment branch at the end of the
file, i.e. it encompasses all modifications on all branches except for `local` modifications for
which only the main branch is included.
-/
inductive EnvExtension.AsyncMode where
  /--
  Safest access mode, writes and reads the extension state to/from the full `checked`
  environment. This mode ensures the observed state is identical independently of whether or how
  parallel elaboration is used but `getState` will block on all prior environment branches by
  waiting for `checked`. `setState` and `modifyState` do not block.

  While a safe fallback for when `mainOnly` is not sufficient, any extension that reasonably could
  be used in parallel elaboration contexts should opt for a weaker mode to avoid blocking unless
  there is no way to access the correct state without waiting for all prior environment branches, in
  which case its data management should be restructured if at all possible.
  -/
  | sync
  /--
  Accesses only the state of the current environment branch. Modifications on other branches are not
  visible and are ultimately discarded except for the main branch. Provides the fastest accessors,
  will never block.

  This mode is particularly suitable for extensions where state does not escape from lexical scopes
  even without parallelism, e.g. `ScopedEnvExtension`s when setting local entries.
  -/
  | local
  /--
  Default access mode. Like `local` but panics when trying to modify the state on anything but the
  main environment branch. For extensions that fulfill this requirement, all modes functionally
  coincide with `local` but this is the safest and most efficient choice in that case, preventing
  accidental misuse.

  This mode is suitable for extensions that are modified only at the command elaboration level
  before any environment forks in the command, and in particular for extensions that are modified
  only at the very beginning of the file.
  -/
  | mainOnly
  /--
  Accumulates modifications in the `checked` environment like `sync`, but `get/modify/setState` will
  panic instead of blocking unless their `asyncDecl` parameter is specified, which will access the
  state of the environment branch corresponding to the passed declaration name, if any; see
  `AsyncBranch` for a description of the specific state accessed. In other words, at most the
  environment branch corresponding to that declaration will be blocked on instead of all prior
  branches. The local state can still be accessed by calling `getState` with mode `local`
  explicitly.

  This mode is suitable for extensions with map-like state where the key uniquely identifies the
  top-level declaration where it could have been set, e.g. because the key on modification is always
  the surrounding declaration's name. In particular, this mode is closest to how the environment's
  own constant map works which provides `findAsync?` for block-avoiding access.
  -/
  | async (branch : AsyncBranch)
  deriving Inhabited

abbrev ReplayFn (σ : Type) :=
  (oldState : σ) → (newState : σ) → (newConsts : List Name) → σ → σ

/--
Environment extension, can only be generated by `registerEnvExtension` that allocates a unique index
for this extension into each environment's extension state's array.
-/
structure EnvExtension (σ : Type) where private mk ::
  idx       : Nat
  mkInitial : IO σ
  asyncMode : EnvExtension.AsyncMode
  /--
  Optional function that, given state before and after realization and newly added constants,
  replays this change onto a state from another (derived) environment. This function is used only
  when making changes to an extension inside a `realizeConst` call, in which case it must be
  present.
  -/
  replay?   : Option (ReplayFn σ)
  deriving Inhabited

namespace EnvExtension

private builtin_initialize envExtensionsRef : IO.Ref (Array (EnvExtension EnvExtensionState)) ← IO.mkRef #[]

/--
  User-defined environment extensions are declared using the `initialize` command.
  This command is just syntax sugar for the `init` attribute.
  When we `import` lean modules, the vector stored at `envExtensionsRef` may increase in size because of
  user-defined environment extensions. When this happens, we must adjust the size of the `env.extensions`.
  This method is invoked when processing `import`s.
-/
partial def ensureExtensionsArraySize (exts : Array EnvExtensionState) : IO (Array EnvExtensionState) := do
  loop exts.size exts
where
  loop (i : Nat) (exts : Array EnvExtensionState) : IO (Array EnvExtensionState) := do
    let envExtensions ← envExtensionsRef.get
    if h : i < envExtensions.size then
      let s ← envExtensions[i].mkInitial
      let exts := exts.push s
      loop (i + 1) exts
    else
      return exts

private def invalidExtMsg := "invalid environment extension has been accessed"

private unsafe def setStateImpl {σ} (ext : EnvExtension σ) (exts : Array EnvExtensionState) (s : σ) : Array EnvExtensionState :=
  if h : ext.idx < exts.size then
    exts.set ext.idx (unsafeCast s)
  else
    -- do not return an empty array on panic, avoiding follow-up out-of-bounds accesses
    have : Inhabited (Array EnvExtensionState) := ⟨exts⟩
    panic! invalidExtMsg

private unsafe def modifyStateImpl {σ : Type} (ext : EnvExtension σ) (exts : Array EnvExtensionState) (f : σ → σ) : Array EnvExtensionState :=
  if ext.idx < exts.size then
    exts.modify ext.idx fun s =>
      let s : σ := unsafeCast s
      let s : σ := f s
      unsafeCast s
  else
    -- do not return an empty array on panic, avoiding follow-up out-of-bounds accesses
    have : Inhabited (Array EnvExtensionState) := ⟨exts⟩
    panic! invalidExtMsg

private unsafe def getStateImpl {σ} [Inhabited σ] (ext : EnvExtension σ) (exts : Array EnvExtensionState) : σ :=
  if h : ext.idx < exts.size then
    unsafeCast exts[ext.idx]
  else
    panic! invalidExtMsg

def mkInitialExtStates : IO (Array EnvExtensionState) := do
  let exts ← envExtensionsRef.get
  exts.mapM fun ext => ext.mkInitial

/--
Checks whether `modifyState (asyncDecl := declName)` may be called on an async environment
extension; see `AsyncMode.async` for details.
-/
def asyncMayModify (ext : EnvExtension σ) (env : Environment) (asyncDecl : Name)
    (asyncMode := ext.asyncMode) : Bool :=
  env.asyncCtx?.all fun ctx =>
    match asyncMode with
    -- The main env's async context, if any, should be a strict prefix of `asyncDecl`. This does not
    -- conclusively check that we are not in some parent branch of `mainEnv` but it covers the most
    -- common case of confusing `mainEnv` and `asyncEnv`.
    | .async .mainEnv => ctx.mayContain asyncDecl && ctx.declPrefix != asyncDecl
    -- The async env's async context should either be `asyncDecl` itself or `asyncDecl` is a nested
    -- declaration that is not itself async.
    | .async .asyncEnv => ctx.declPrefix == asyncDecl ||
      (ctx.mayContain asyncDecl && (env.findAsyncConst? asyncDecl).any (·.exts?.isNone))
    | _ => true

/--
Applies the given function to the extension state. See `AsyncMode` for details on how modifications
from different environment branches are reconciled.

Note that in modes `sync` and `async`, `f` will be called twice, on the local and on the `checked`
state.
-/
def modifyState {σ : Type} (ext : EnvExtension σ) (env : Environment) (f : σ → σ)
    (asyncMode := ext.asyncMode) (asyncDecl : Name := .anonymous) : Environment := Id.run do
  -- for panics
  let _ : Inhabited Environment := ⟨env⟩
  -- safety: `ext`'s constructor is private, so we can assume the entry at `ext.idx` is of type `σ`
  match asyncMode with
  | .mainOnly =>
    if let some asyncCtx := env.asyncCtx? then
      return panic! s!"environment extension is marked as `mainOnly` but used in \
        {if env.isRealizing then "realization" else "async"} context '{asyncCtx.declPrefix}'"
    return { env with base.private.extensions := unsafe ext.modifyStateImpl env.base.private.extensions f }
  | .local =>
    return { env with base.private.extensions := unsafe ext.modifyStateImpl env.base.private.extensions f }
  | _ =>
    if asyncMode matches .async _ then
      if asyncDecl.isAnonymous then
        return panic! "called on `async` extension, must set `asyncDecl` in that case"

      if let some ctx := env.asyncCtx? then
        if !ext.asyncMayModify (asyncMode := asyncMode) env asyncDecl then
          return panic! s!"`asyncDecl` `{asyncDecl}` is outside current context {ctx.declPrefix}"

    if ext.replay?.isNone then
      if let some (n :: _) := env.asyncCtx?.map (·.realizingStack) then
        return panic! s!"environment extension must set `replay?` field to be \
          used in realization context '{n}'"
    env.modifyCheckedAsync fun env =>
      { env with extensions := unsafe ext.modifyStateImpl env.extensions f }

/--
Sets the extension state to the given value. See `AsyncMode` for details on how modifications from
different environment branches are reconciled.
-/
def setState {σ : Type} (ext : EnvExtension σ) (env : Environment) (s : σ) (asyncMode := ext.asyncMode) : Environment :=
  inline <| modifyState (asyncMode := asyncMode) ext env fun _ => s

-- `unsafe` fails to infer `Nonempty` here
private unsafe def getStateUnsafe {σ : Type} [Inhabited σ] (ext : EnvExtension σ)
    (env : Environment) (asyncMode := ext.asyncMode) (asyncDecl : Name := .anonymous) : σ := Id.run do
  -- safety: `ext`'s constructor is private, so we can assume the entry at `ext.idx` is of type `σ`
  match asyncMode with
  | .sync => ext.getStateImpl env.checked.get.extensions
  | .async branch =>
    if asyncDecl.isAnonymous then
      panic! "called on `async` extension, must set `asyncDecl` \
        or pass `(asyncMode := .local)` to explicitly access local state"

    -- analogous structure to `findAsync?`; see there
    -- safety: `ext`'s constructor is private, so we can assume the entry at `ext.idx` is of type `σ`
    if env.base.get env |>.constants.contains asyncDecl then
      return ext.getStateImpl env.base.private.extensions

    -- specialization of the following branch, nested async decls are rare
    if let some c := env.asyncConsts.find? asyncDecl then
      match branch with
      | .asyncEnv =>
        if let some exts := c.exts? then
          return ext.getStateImpl exts.get
        else
          return ext.getStateImpl env.base.private.extensions
      | .mainEnv =>
        if c.isRealized then
          if let some exts := c.exts? then
            return ext.getStateImpl exts.get
        else
          return ext.getStateImpl env.base.private.extensions

    if let some (c, parent?) := env.asyncConsts.findRecAndParent? asyncDecl then
      -- If `parent?` is `none`, the current branch is the parent
      let parentExts? := match parent? with
        | some c => c.exts?
        | none   => some <| .pure env.base.private.extensions
      if let some exts := (match branch with
          -- If the constant is not async, fall back to parent
          | .asyncEnv => c.exts? <|> parentExts?
          -- If the constant is realized, parent branch is empty and we should always look at `c`. In
          -- this specific case, accessing the latter will in particular not block longer than the
          -- former.
          | .mainEnv => if c.isRealized then c.exts? else parentExts?) then
        return ext.getStateImpl exts.get
      -- NOTE: if `exts?` is `none`, we should *not* try the following, more expensive branches that
      -- will just come to the same conclusion
    else if let some c := env.allRealizations.get.find? asyncDecl then
      if let some exts := c.exts? then
        return ext.getStateImpl exts.get
    -- fallback; we could enforce that `asyncDecl` and its extension state always exist but the
    -- upside of doing is unclear and it is not true in e.g. the compiler. One alternative would be
    -- to add a `getState?` that does not panic in such cases.
    ext.getStateImpl env.base.private.extensions
  | _         => ext.getStateImpl env.base.private.extensions

/--
Returns the current extension state. See `AsyncMode` for details on how modifications from
different environment branches are reconciled.

Overriding the extension's default `AsyncMode` is usually not recommended and should be considered
only for important optimizations.
-/
@[implemented_by getStateUnsafe]
opaque getState {σ : Type} [Inhabited σ] (ext : EnvExtension σ) (env : Environment)
  (asyncMode := ext.asyncMode) (asyncDecl : Name := .anonymous) : σ

end EnvExtension

/-- Environment extensions can only be registered during initialization.
   Reasons:
   1- Our implementation assumes the number of extensions does not change after an environment object is created.
   2- We do not use any synchronization primitive to access `envExtensionsRef`.

   Note that by default, extension state is *not* stored in .olean files and will not propagate across `import`s.
   For that, you need to register a persistent environment extension. -/
def registerEnvExtension {σ : Type} (mkInitial : IO σ)
    (replay? : Option (ReplayFn σ) := none)
    (asyncMode : EnvExtension.AsyncMode := .mainOnly) : IO (EnvExtension σ) := do
  unless (← initializing) do
    throw (IO.userError "failed to register environment, extensions can only be registered during initialization")
  let exts ← EnvExtension.envExtensionsRef.get
  let idx := exts.size
  let ext : EnvExtension σ := { idx, mkInitial, asyncMode, replay? }
  -- safety: `EnvExtensionState` is opaque, so we can upcast to it
  EnvExtension.envExtensionsRef.modify fun exts => exts.push (unsafe unsafeCast ext)
  pure ext

private def mkInitialExtensionStates : IO (Array EnvExtensionState) := EnvExtension.mkInitialExtStates

@[export lean_mk_empty_environment]
def mkEmptyEnvironment (trustLevel : UInt32 := 0) : IO Environment := do
  let initializing ← IO.initializing
  if initializing then throw (IO.userError "environment objects cannot be created during initialization")
  let exts ← mkInitialExtensionStates
  return {
    base := .const {
      const2ModIdx    := {}
      -- Make sure we return a sharing-friendly map set to stage 2, like in `finalizeImport`.
      constants       := SMap.empty.switch
      header          := { trustLevel }
      extensions      := exts
      irBaseExts      := exts
    }
    importRealizationCtx? := none
  }

structure PersistentEnvExtensionState (α : Type) (σ : Type) where
  importedEntries : Array (Array α)  -- entries per imported module
  state : σ

structure ImportM.Context where
  env  : Environment
  opts : Options

abbrev ImportM := ReaderT Lean.ImportM.Context IO

/-- The level of information to save/load. Each level includes all previous ones. -/
inductive OLeanLevel where
  /-- Information from exported contexts. -/
  | exported
  /-- Environment extension state for the language server. -/
  | server
  /-- Private module data. -/
  | «private»
deriving DecidableEq, Ord, Repr

instance : LE OLeanLevel := leOfOrd
instance : LT OLeanLevel := ltOfOrd

/--
An environment extension with support for storing/retrieving entries from a .olean file.
 - α is the type of the entries that are stored in .olean files.
 - β is the type of values used to update the state.
 - σ is the actual state.

For most extensions, α and β coincide. `α` and `β` do not coincide for extensions where the data
used to update the state contains elements which cannot be stored in files (for example, closures).

During elaboration of a module, state of type `σ` can be both read and written. When elaboration is
complete, the state of type `σ` is converted to serialized state of type `Array α` by
`exportEntriesFn`. To read the current module's state, use `PersistentEnvExtension.getState`. To
modify it, use `PersistentEnvExtension.addEntry`, with an `addEntryFn` that performs the appropriate
modification.

When a module is loaded, the values saved by all of its dependencies for this
`PersistentEnvExtension` are available as an `Array (Array α)` via the environment extension,
with one array per transitively imported module. The state of type `σ` used in the current module
can be initialized from these imports by specifying a suitable `addImportedFn`. The `addImportedFn`
runs at the beginning of elaboration for every module, so it's usually better for performance to
query the array of imported modules directly, because only a fraction of imported entries is usually
queried during elaboration of a module.

The most typical pattern for using `PersistentEnvExtension` is to set `σ` to a datatype such as
`NameMap` that efficiently tracks data for the current module. Then, in `exportEntriesFn`, this type
is converted to an array of pairs, sorted by the key. Given `ext : PersistentEnvExtension α β σ` and
`env : Environment`, the complete array of imported entries sorted by module index can be obtained
using `(ext.toEnvExtension.getState env).importedEntries`. To query the extension for some constant
name `n`, first use `env.getModuleIdxFor? n`. If it returns `none`, look up `n` in the current
module's state (the `NameMap`). If it returns `some idx`, use `ext.getModuleEntries env idx` to get
the array of entries for `n`'s defining module, and query it using `Array.binSearch`. This pattern
imposes a constraint that the extension can only track metadata that is declared in the same module
as the definition to which it applies; relaxing this restriction can make queries slower due to
needing to search _all_ modules. If it is necessary to search all modules, it is usually better to
initialize the state of type `σ` once from all imported entries and choose a more efficient search
datastructure for it.

Note that `addEntryFn` is not in `IO`. This is intentional, and allows us to write simple functions
such as
```
def addAlias (env : Environment) (a : Name) (e : Name) : Environment :=
aliasExtension.addEntry env (a, e)
```
without using `IO`. We have many functions like `addAlias`.
-/
structure PersistentEnvExtension (α : Type) (β : Type) (σ : Type) where
  toEnvExtension  : EnvExtension (PersistentEnvExtensionState α σ)
  name            : Name
  addImportedFn   : Array (Array α) → ImportM σ
  addEntryFn      : σ → β → σ
  /--
  Function to transform state into data that should be imported into other modules. When using the
  module system without `import all`, `OLeanLevel.exported` is imported, else `OLeanLevel.private`.
  Additionally, when using the module system in the language server, the `OLeanLevel.server` data is
  accessible via `getModuleEntries (level := .server)`. By convention, each level should include all
  data of previous levels.

  This function is run after elaborating the file and joining all asynchronous threads. It is run
  once for each level when the module system is enabled, otherwise once for `private`.
  -/
  exportEntriesFn : Environment → σ → OLeanLevel → Array α
  statsFn         : σ → Format

instance {α σ} [Inhabited σ] : Inhabited (PersistentEnvExtensionState α σ) :=
  ⟨{importedEntries := #[], state := default }⟩

instance {α β σ} [Inhabited σ] : Inhabited (PersistentEnvExtension α β σ) where
  default := {
     toEnvExtension := default,
     name := default,
     addImportedFn := fun _ => default,
     addEntryFn := fun s _ => s,
     exportEntriesFn := fun _ _ _ => #[],
     statsFn := fun _ => Format.nil
  }

namespace PersistentEnvExtension

/--
Returns the data saved by `ext.exportEntriesFn` when `m` was elaborated. See docs on the function for
details. When using the module system, `level` can be used to select the level of data to retrieve,
but is limited to the maximum level actually imported: `exported` on the cmdline and `server` in the
language server. Higher levels will return the data of the maximum imported level.
-/
def getModuleEntries {α β σ : Type} [Inhabited σ] (ext : PersistentEnvExtension α β σ)
    (env : Environment) (m : ModuleIdx) (level := OLeanLevel.exported) : Array α :=
  let exts := match level with
    | .exported => env.base.private.extensions
    | _         => env.serverBaseExts
  -- safety: as in `getStateUnsafe`
  unsafe (ext.toEnvExtension.getStateImpl exts).importedEntries[m]!

/-- Retrieves additional IR extension state for the interpreter. -/
def getModuleIREntries {α β σ : Type} [Inhabited σ] (ext : PersistentEnvExtension α β σ)
    (env : Environment) (m : ModuleIdx) : Array α :=
  -- safety: as in `getStateUnsafe`
  unsafe (ext.toEnvExtension.getStateImpl env.base.private.irBaseExts).importedEntries[m]!

def addEntry {α β σ : Type} (ext : PersistentEnvExtension α β σ) (env : Environment) (b : β)
    (asyncMode := ext.toEnvExtension.asyncMode) (asyncDecl : Name := .anonymous) : Environment :=
  ext.toEnvExtension.modifyState (asyncMode := asyncMode) (asyncDecl := asyncDecl) env fun s =>
    let state   := ext.addEntryFn s.state b;
    { s with state := state }

/-- Get the current state of the given extension in the given environment. -/
def getState {α β σ : Type} [Inhabited σ] (ext : PersistentEnvExtension α β σ) (env : Environment)
    (asyncMode := ext.toEnvExtension.asyncMode) (asyncDecl : Name := .anonymous) : σ :=
  (ext.toEnvExtension.getState (asyncMode := asyncMode) (asyncDecl := asyncDecl) env).state

/-- Set the current state of the given extension in the given environment. -/
def setState {α β σ : Type} (ext : PersistentEnvExtension α β σ) (env : Environment) (s : σ) : Environment :=
  ext.toEnvExtension.modifyState env fun ps => { ps with  state := s }

/-- Modify the state of the given extension in the given environment by applying the given function. -/
def modifyState {α β σ : Type} (ext : PersistentEnvExtension α β σ) (env : Environment) (f : σ → σ)
    (asyncMode := ext.toEnvExtension.asyncMode) (asyncDecl : Name := Name.anonymous) : Environment :=
  ext.toEnvExtension.modifyState (asyncMode := asyncMode) (asyncDecl := asyncDecl) env fun ps => { ps with state := f (ps.state) }

end PersistentEnvExtension

builtin_initialize persistentEnvExtensionsRef : IO.Ref (Array (PersistentEnvExtension EnvExtensionEntry EnvExtensionEntry EnvExtensionState)) ← IO.mkRef #[]

-- Helper structure to enable cyclic default values of `exportEntriesFn` and `exportEntriesFnEx`.
structure PersistentEnvExtensionDescrCore (α β σ : Type) where
  name              : Name := by exact decl_name%
  mkInitial         : IO σ
  addImportedFn     : Array (Array α) → ImportM σ
  addEntryFn        : σ → β → σ
  exportEntriesFnEx : Environment → σ → OLeanLevel → Array α
  statsFn           : σ → Format := fun _ => Format.nil
  asyncMode         : EnvExtension.AsyncMode := .mainOnly
  replay?           : Option (ReplayFn σ) := none

attribute [inherit_doc PersistentEnvExtension.exportEntriesFn]
  PersistentEnvExtensionDescrCore.exportEntriesFnEx

/--
Auxiliary function to signal to the structure instance elaborator that `default` should be used as
the default value for a field but only if `_otherField` has been given, which is added as an
artificial dependency.
-/
def useDefaultIfOtherFieldGiven (default : α) (_otherField : β) : α :=
  default

structure PersistentEnvExtensionDescr (α β σ : Type) extends PersistentEnvExtensionDescrCore α β σ where
  -- The cyclic default values force the user to specify at least one of the two following fields.
  /--
  Obsolete simpler version of `exportEntriesFnEx`. Its value is ignored if the latter is also
  specified.
  -/
  exportEntriesFn : σ → Array α := useDefaultIfOtherFieldGiven (fun _ => #[]) exportEntriesFnEx
  exportEntriesFnEx := fun _ s _ => exportEntriesFn s

unsafe def registerPersistentEnvExtensionUnsafe {α β σ : Type} [Inhabited σ] (descr : PersistentEnvExtensionDescr α β σ) : IO (PersistentEnvExtension α β σ) := do
  let pExts ← persistentEnvExtensionsRef.get
  if pExts.any (fun ext => ext.name == descr.name) then throw (IO.userError s!"invalid environment extension, '{descr.name}' has already been used")
  let replay? := descr.replay?.map fun replay =>
    fun oldState newState newConsts s => { s with state := replay oldState.state newState.state newConsts s.state }
  let ext ← registerEnvExtension (asyncMode := descr.asyncMode) (replay? := replay?) do
    let initial ← descr.mkInitial
    let s : PersistentEnvExtensionState α σ := {
      importedEntries := #[],
      state           := initial
    }
    pure s
  let pExt : PersistentEnvExtension α β σ := {
    toEnvExtension  := ext,
    name            := descr.name,
    addImportedFn   := descr.addImportedFn,
    addEntryFn      := descr.addEntryFn,
    exportEntriesFn := descr.exportEntriesFnEx,
    statsFn         := descr.statsFn
  }
  persistentEnvExtensionsRef.modify fun pExts => pExts.push (unsafeCast pExt)
  return pExt

@[implemented_by registerPersistentEnvExtensionUnsafe]
opaque registerPersistentEnvExtension {α β σ : Type} [Inhabited σ] (descr : PersistentEnvExtensionDescr α β σ) : IO (PersistentEnvExtension α β σ)

/--
Stores each given module data in the respective file name. Objects shared with prior parts are not
duplicated. Thus the data cannot be loaded with individual `readModuleData` calls but must loaded by
passing (a prefix of) the file names to `readModuleDataParts`. `mod` is used to determine an
arbitrary but deterministic base address for `mmap`.
-/
@[extern "lean_save_module_data_parts"]
opaque saveModuleDataParts (mod : @& Name) (parts : @& Array (System.FilePath × ModuleData)) : IO Unit

/--
Loads the module data from the given file names. The files must be (a prefix of) the result of a
`saveModuleDataParts` call.
-/
@[extern "lean_read_module_data_parts"]
opaque readModuleDataParts (fnames : @& Array System.FilePath) : IO (Array (ModuleData × CompactedRegion))

def saveModuleData (fname : System.FilePath) (mod : Name) (data : ModuleData) : IO Unit :=
  saveModuleDataParts mod #[(fname, data)]

def readModuleData (fname : @& System.FilePath) : IO (ModuleData × CompactedRegion) := do
  let parts ← readModuleDataParts #[fname]
  assert! parts.size == 1
  let some part := parts[0]? | unreachable!
  return part

/--
  Free compacted regions of imports. No live references to imported objects may exist at the time of invocation; in
  particular, `env` should be the last reference to any `Environment` derived from these imports. -/
@[noinline, export lean_environment_free_regions]
unsafe def Environment.freeRegions (env : Environment) : IO Unit :=
  /-
    NOTE: This assumes `env` is not inferred as a borrowed parameter, and is freed after extracting the `header` field.
    Otherwise, we would encounter undefined behavior when the constant map in `env`, which may reference objects in
    compacted regions, is freed after the regions.

    In the currently produced IR, we indeed see:
    ```
      def Lean.Environment.freeRegions (x_1 : obj) (x_2 : obj) : obj :=
        let x_3 : obj := proj[3] x_1;
        inc x_3;
        dec x_1;
        ...
    ```

    TODO: statically check for this. -/
  env.header.regions.forM CompactedRegion.free

def OLeanLevel.adjustFileName (base : System.FilePath) : OLeanLevel → System.FilePath
  | .exported => base
  | .server   => base.addExtension "server"
  | .private  => base.addExtension "private"

private def looksLikeOldCodegenName : Name → Bool
  | .str _ s => s.startsWith "_cstage" || s.startsWith "_spec_" || s.startsWith "_elambda"
  | _        => false

@[extern "lean_get_ir_extra_const_names"]
private opaque getIRExtraConstNames (env : Environment) (level : OLeanLevel) (includeDecls := false) : Array Name

def mkModuleData (env : Environment) (level : OLeanLevel := .private) : IO ModuleData := do
  let env := env.setExporting (level != .private)
  let pExts ← persistentEnvExtensionsRef.get
  let entries := pExts.map fun pExt => Id.run do
    -- get state from `checked` at the end if `async`; it would otherwise panic
    let mut asyncMode := pExt.toEnvExtension.asyncMode
    if asyncMode matches .async _ then
      asyncMode := .sync
    let state := pExt.getState (asyncMode := asyncMode) env
    (pExt.name, pExt.exportEntriesFn env state level)
  let kenv := env.toKernelEnv
  let constNames := kenv.constants.foldStage2 (fun names name _ => names.push name) #[]
  -- not all kernel constants may be exported at `level < .private`
  let constants := if level == .private then
    -- (this branch makes very sure all kernel constants are exported eventually)
    kenv.constants.foldStage2 (fun cs _ c => cs.push c) #[]
  else
    constNames.filterMap (fun n =>
        env.find? n <|>
        guard (looksLikeOldCodegenName n) *> kenv.find? n)
      -- While `constants.foldStage2` itself results in a deterministic ordering, then filtering out
      -- some elements leaves the order of remaining dependent on those filtered elements, which
      -- would make `.olean` output dependent on `.olean.private`, so we re-sort them here.
      |>.qsort (lt := fun c₁ c₂ => c₁.name.quickCmp c₂.name == .lt)
  let constNames := constants.map (·.name)
  return { env.header with
    extraConstNames := getIRExtraConstNames env level
    constNames, constants, entries
  }

@[extern "lean_ir_export_entries"]
private opaque exportIREntries (env : Environment) : Array (Name × Array EnvExtensionEntry)

private def mkIRData (env : Environment) : ModuleData :=
  -- TODO: should we use a more specific/efficient data format for IR?
  { env.header with
    entries := exportIREntries env
    constants := default
    constNames := default
    -- make sure to include all names in case only `.ir` is loaded
    extraConstNames := getIRExtraConstNames env .private (includeDecls := true)
  }

def writeModule (env : Environment) (fname : System.FilePath) : IO Unit := do
  if env.header.isModule then
    let mkPart (level : OLeanLevel) :=
      return (level.adjustFileName fname, (← mkModuleData env level))
    saveModuleDataParts env.mainModule #[
      (← mkPart .exported),
      (← mkPart .server),
      (← mkPart .private)]
    -- Make sure to change the module name so we derive a different base address
    saveModuleData (fname.withExtension "ir") (env.mainModule ++ `ir) (mkIRData env)
  else
    saveModuleData fname env.mainModule (← mkModuleData env)

/--
Construct a mapping from persistent extension name to extension index at the array of persistent extensions.
We only consider extensions starting with index `>= startingAt`.
-/
def mkExtNameMap (startingAt : Nat) : IO (Std.HashMap Name Nat) := do
  let descrs ← persistentEnvExtensionsRef.get
  let mut result := {}
  for h : i in startingAt...descrs.size do
    let descr := descrs[i]
    result := result.insert descr.name i
  return result

private def setImportedEntries (states : Array EnvExtensionState) (mods : Array ModuleData)
    (startingAt : Nat := 0) : IO (Array EnvExtensionState) := do
  let mut states := states
  let extDescrs ← persistentEnvExtensionsRef.get
  /- For extensions starting at `startingAt`, ensure their `importedEntries` array have size `mods.size`. -/
  for extDescr in extDescrs[startingAt...*] do
    -- safety: as in `modifyState`
    states := unsafe extDescr.toEnvExtension.modifyStateImpl states fun s =>
      { s with importedEntries := .replicate mods.size #[] }
  /- For each module `mod`, and `mod.entries`, if the extension name is one of the extensions after `startingAt`, set `entries` -/
  let extNameIdx ← mkExtNameMap startingAt
  for h : modIdx in *...mods.size do
    let mod := mods[modIdx]
    for (extName, entries) in mod.entries do
      if let some entryIdx := extNameIdx[extName]? then
        -- safety: as in `modifyState`
        states := unsafe extDescrs[entryIdx]!.toEnvExtension.modifyStateImpl states fun s =>
          { s with importedEntries := s.importedEntries.set! modIdx entries }
  return states

/--
  "Forward declaration" needed for updating the attribute table with user-defined attributes.
  User-defined attributes are declared using the `initialize` command. The `initialize` command is just syntax sugar for the `init` attribute.
  The `init` attribute is initialized after the `attributeExtension` is initialized. We cannot change the order since the `init` attribute is an attribute,
  and requires this extension.
  The `attributeExtension` initializer uses `attributeMapRef` to initialize the attribute mapping.
  When we a new user-defined attribute declaration is imported, `attributeMapRef` is updated.
  Later, we set this method with code that adds the user-defined attributes that were imported after we initialized `attributeExtension`.
-/
@[extern "lean_update_env_attributes"] opaque updateEnvAttributes : Environment → IO Environment
/-- "Forward declaration" for retrieving the number of builtin attributes. -/
@[extern "lean_get_num_attributes"] opaque getNumBuiltinAttributes : IO Nat

@[extern "lean_run_init_attrs"]
private opaque runInitAttrs (env : Environment) (opts : Options) : IO Unit

private def ensureExtensionsArraySize (env : Environment) : IO Environment := do
  let exts ← EnvExtension.ensureExtensionsArraySize env.base.private.extensions
  return env.modifyCheckedAsync ({ · with extensions := exts })

private partial def finalizePersistentExtensions (env : Environment) (mods : Array ModuleData) (opts : Options) : IO Environment := do
  loop 0 env
where
  loop (i : Nat) (env : Environment) : IO Environment := do
    -- Recall that the size of the array stored `persistentEnvExtensionRef` may increase when we import user-defined environment extensions.
    let pExtDescrs ← persistentEnvExtensionsRef.get
    if h : i < pExtDescrs.size then
      let extDescr := pExtDescrs[i]
      -- Use `sync` to avoid `async` checks; there is only one environment branch at this point
      -- anyway.
      let s := extDescr.toEnvExtension.getState (asyncMode := .sync) env
      let prevSize := (← persistentEnvExtensionsRef.get).size
      let prevAttrSize ← getNumBuiltinAttributes
      let newState ← extDescr.addImportedFn s.importedEntries { env := env, opts := opts }
      let mut env := extDescr.toEnvExtension.setState (asyncMode := .sync) env { s with state := newState }
      if extDescr.name == `Lean.regularInitAttr then
        -- Run `[init]` attributes now. We do this after `setState` so `runInitAttrs` can access
        -- `getModule(IR)Entries` but we should also do it before attempting to run user-defined
        -- extensions further down in `pExtDescrs` so they can access initialized declarations.
        runInitAttrs env opts
      env ← ensureExtensionsArraySize env
      if (← persistentEnvExtensionsRef.get).size > prevSize || (← getNumBuiltinAttributes) > prevAttrSize then
        -- This branch is executed when `pExtDescrs[i]` is the extension associated with the `init` attribute, and
        -- a user-defined persistent extension is imported.
        -- Thus, we invoke `setImportedEntries` to update the array `importedEntries` with the entries for the new extensions.
        env := env.setCheckedSync { env.base.private with extensions := (← setImportedEntries env.base.private.extensions mods prevSize) }
        -- See comment at `updateEnvAttributesRef`
        env ← updateEnvAttributes env
      loop (i + 1) env
    else
      return env

private structure ImportedModule extends EffectiveImport where
  /-- All loaded incremental compacted regions from `.olean*`. -/
  parts     : Array (ModuleData × CompactedRegion)
  /-- `.ir` data, if loaded. -/
  irData?   : Option (ModuleData × CompactedRegion)
  /-- If true, `.olean*` data should be imported. -/
  needsData : Bool
  /-- If true, IR is loaded transitively. -/
  needsIRTrans : Bool

/-- The main module data that will eventually be used to construct the publicly accessible constants. -/
private def ImportedModule.publicModule? (self : ImportedModule) : Option ModuleData := do
  if self.needsData then
    self.parts[0]?.map (·.1)
  else
    -- (should not have any constants)
    self.irData?.map (·.1)

private def ImportedModule.getData? (self : ImportedModule) (level : OLeanLevel) : Option ModuleData := do
  -- Without the module system, we only have the exported level.
  let level := if (← self.publicModule?).isModule then level else .exported
  self.parts[level.ctorIdx]?.map (·.1)

/-- The main module data that will eventually be used to construct the kernel environment. -/
private def ImportedModule.mainModule? (self : ImportedModule) : Option ModuleData :=
  if self.needsData then
    self.getData? (if self.importAll then .private else .exported)
  else
    self.irData?.map (·.1)

/-- The module data that should be used for server purposes. -/
private def ImportedModule.serverData? (self : ImportedModule) (level : OLeanLevel) :
    Option ModuleData :=
  -- fall back to `exported` outside the server
  self.getData? (if level ≥ .server then level else .exported)

/-- The module data that should be used for accessing IR for interpretation. -/
private def ImportedModule.interpData? (self : ImportedModule) (level : OLeanLevel) :
    Option ModuleData :=
  if (level < .server && self.irPhases == .runtime) || !self.mainModule?.any (·.isModule) then
    self.mainModule?
  else
    self.irData?.map (·.1)

structure ImportState where
  private moduleNameMap : Std.HashMap Name ImportedModule := {}
  private moduleNames   : Array Name := #[]
deriving Inhabited

/-- Bumps all modules' `isExported` flag to true, intended for use in `shake` only. -/
def ImportState.markAllExported (self : ImportState) : ImportState := Id.run do
  let mut self := self
  for (k, v) in self.moduleNameMap do
    unless v.isExported do
      self := { self with moduleNameMap := self.moduleNameMap.insert k { v with isExported := true } }
  return self

def throwAlreadyImported (s : ImportState) (const2ModIdx : Std.HashMap Name ModuleIdx) (modIdx : Nat) (cname : Name) : IO α := do
  let modName := s.moduleNames[modIdx]!
  let constModName := s.moduleNames[const2ModIdx[cname]!.toNat]!
  throw <| IO.userError s!"import {modName} failed, environment already contains '{cname}' from {constModName}"

abbrev ImportStateM := StateRefT ImportState IO

@[inline] nonrec def ImportStateM.run (x : ImportStateM α) (s : ImportState := default) : IO (α × ImportState) :=
  x.run s

private def findOLeanParts (mod : Name) : IO (Array System.FilePath) := do
  let mFile ← findOLean mod
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {mod} does not exist"
  let mut fnames := #[mFile]
  -- Opportunistically load all available parts.
  -- Necessary because the import level may be upgraded a later import.
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then
      fnames := fnames.push pFile
  return fnames

partial def importModulesCore
    (imports : Array Import) (globalLevel : OLeanLevel := .private)
    (arts : NameMap ImportArtifacts := {}) (isExported : Bool := globalLevel < .private) :
    ImportStateM Unit := do
  go imports (importAll := true) (isExported := isExported) (needsData := true) (needsIRTrans := false)
  if globalLevel < .private then
    for i in imports do
      if let some mod := (← get).moduleNameMap[i.module]?.bind (·.mainModule?) then
        if !mod.isModule then
          throw <| IO.userError s!"cannot import non-`module` {i.module} from `module`"
/-
When the module system is disabled for the root, we import all transitively referenced modules and
ignore any module system annotations on the way.

When the module system is enabled for the root, each module may need to be imported at one of the
following levels:

* all: import public information into public scope and private information into private scope
* public: import public information into public scope
* privateAll: import public and private information into private scope
* private: import public information into private scope
* none: do not import any `.olean*`

These levels form a lattice in the following way:

* all > public > private > none
* all > privateAll > private > none

The level at which a module then is to be imported based on the given `import` relations is
determined by the least fixed point of the following rules:

* Root ≥ all
* A ≥ privateAll ∧ A `import all` B → B ≥ privateAll
* A ≥ private ∧ A `public (meta)? import` B → B ≥ private
* A ≥ public ∧ A `public (meta)? import` B → B ≥ public
* A ≥ privateAll ∧ A `(meta)? import` B → B ≥ private

As imports are a DAG, we may need to visit the same module multiple times until its minimum
necessary level is established.

The `meta` flag is special in that it only affects whether IR is needed. The rules for determining
this are as follows:

* A ≥ privateAll ∧ `meta import` B → needsIRTrans(B)
* A ≥ private ∧ A `public meta import` B → needsIRTrans(B)
* needsIRTrans(A) ∧ A `(public)? (meta)? import (all)?` B → needsIRTrans(B)

Note that in particular, A `meta import` B `import` C implies A `meta import` C, but
A `import` B `meta import` C does not.

As a final special case, we also load IR for `import all`, but non-transitively, to provide the same
information as for the current module.

* A ≥ privateAll → needsIR(A)
* needsIRTrans(A) → needsIR(A)

For implementation purposes, we represent elements in the lattice using two flags as follows:

* all = isExported && importAll
* privateAll = !isExported && importAll
* private = !isExported && !importAll
* public = isExported && !importAll

When neither `needsIR(A)` nor `A != none` is true, the module is not visited at all and missing from
the module map.
-/
where
  go (imports : Array Import) (importAll isExported needsData needsIRTrans : Bool) := do
    for i in imports do
      -- `B > none`?
      let needsData := needsData && (i.isExported || importAll)
      -- `B ≥ privateAll`?
      let importAll := globalLevel == .private || importAll && i.importAll
      -- `B ≥ public`?
      let isExported := isExported && i.isExported
      let needsIRTrans := needsIRTrans || needsData && i.isMeta
      let needsIR := needsIRTrans || importAll || globalLevel > .exported
      if !needsData && !needsIR then
        continue

      let irPhases :=
        if importAll then .all
        else if needsIRTrans then .comptime  -- `globalLevel` should *not* be considered here
        else .runtime

      let goRec mod := do
        if let some mod := mod.mainModule? then
          go (importAll := importAll) (isExported := isExported) (needsData := needsData) (needsIRTrans := needsIRTrans) mod.imports

      if let some mod := (← get).moduleNameMap[i.module]? then
        -- when module is already imported, bump flags
        let importAll := importAll || mod.importAll
        let isExported := isExported || mod.isExported
        let needsData := needsData || mod.needsData
        let needsIRTrans := needsIRTrans || mod.needsIRTrans
        let needsIR := needsIRTrans || importAll
        let irPhases := if irPhases == mod.irPhases then irPhases else .all
        let parts ← if needsData && mod.parts.isEmpty then loadData i else pure mod.parts
        let irData? ← if needsIR && mod.irData?.isNone then loadIR? i else pure mod.irData?
        if importAll != mod.importAll || isExported != mod.isExported ||
            needsIRTrans != mod.needsIRTrans || needsData != mod.needsData || irPhases != mod.irPhases then
          modify fun s => { s with moduleNameMap := s.moduleNameMap.insert i.module { mod with
            importAll, isExported, irPhases, parts, irData?, needsData, needsIRTrans }}
          -- bump entire closure
          goRec mod
        continue

      -- newly discovered module
      let parts ← if needsData then loadData i else pure #[]
      let irData? ← if needsIR then loadIR? i else pure none
      let mod := { i with importAll, isExported, irPhases, parts, irData?, needsIRTrans, needsData }
      goRec mod
      modify fun s => { s with
        moduleNameMap := s.moduleNameMap.insert i.module mod
        moduleNames := s.moduleNames.push i.module
      }
  loadData i := do
    let fnames ← if let some arts := arts.find? i.module then
      -- Opportunistically load all available parts.
      -- Producer (e.g., Lake) should limit parts to the proper import level.
      pure (arts.oleanParts (inServer := globalLevel ≥ .server))
    else
      findOLeanParts i.module
    readModuleDataParts fnames
  loadIR? i := do
    let irFile? ← if let some arts := arts.find? i.module then
      pure arts.ir?
    else
      let irFile := (← findOLean i.module).withExtension "ir"
      pure (guard (← irFile.pathExists) *> irFile)
    irFile?.mapM (readModuleData ·)

/--
Returns `true` if `cinfo₁` and `cinfo₂` represent the same theorem/axiom, with `cinfo₁` potentially
being a richer representation; under the module system, a theorem may be weakened to an axiom when
exported. We allow different modules to prove the same theorem.

Motivation: We want to generate equational theorems on demand and potentially
in different files, and we want them to have non-private names.
We may add support for other kinds of definitions in the future. For now, theorems are
sufficient for our purposes.

We may have to revise this design decision and eagerly generate equational theorems when
we implement the module system.

Remark: we do not check whether the theorem `value` field match. This feature is useful and
ensures the proofs for equational theorems do not need to be identical. This decision
relies on the fact that theorem types are propositions, we have proof irrelevance,
and theorems are (mostly) opaque in Lean. For `Acc.rec`, we may unfold theorems
during type-checking, but we are assuming this is not an issue in practice,
and we are planning to address this issue in the future.
-/
private def subsumesInfo (constMap : Std.HashMap Name ConstantInfo) (cinfo₁ cinfo₂ : ConstantInfo) : Bool :=
  cinfo₁.name == cinfo₂.name &&
    cinfo₁.type == cinfo₂.type &&
    cinfo₁.levelParams == cinfo₂.levelParams &&
    match cinfo₁, cinfo₂ with
    | .thmInfo tval₁, .thmInfo tval₂ => tval₁.all == tval₂.all
    | .thmInfo tval₁, .axiomInfo aval₂ => tval₁.all == [aval₂.name] && !aval₂.isUnsafe
    | .axiomInfo aval₁, .axiomInfo aval₂ =>
      -- In this case, we cannot a priori assume that both axioms came from theorems and thus their
      -- former bodies are irrelevant - they could be both from definitions with different bodies
      -- that were used to derive statements that would be contradictory if the axioms were merged.
      -- Thus we do a rough, pure approximation of `Lean.Meta.isProp` that is sufficient for the
      -- restricted types we use for realizable theorems and ensures the former bodies of the two
      -- axioms must be irrelevant after all.
      aval₁.isUnsafe == aval₂.isUnsafe && isPropCheap aval₁.type
    | _, _ => false
where
  /--
  Check if `ty = ∀ ..., p xs...` and `p : ∀ args..., Prop` where `xs` and `args` are of the same
  length.
  -/
  isPropCheap (ty : Expr) : Bool := Id.run do
    let mut ty := ty
    while ty.isForall do
      let .forallE (body := body) .. := ty | return false
      ty := body
    let .const n .. := ty.getAppFn | return false
    let some decl := constMap[n]? | return false
    let mut p := decl.type
    for _ in 0...ty.getAppNumArgs do
      let .forallE (body := body) .. := p | return false
      p := body
    p.isProp

/--
Constructs environment from `importModulesCore` results.

See also `importModules` for parameter documentation.
-/
def finalizeImport (s : ImportState) (imports : Array Import) (opts : Options) (trustLevel : UInt32 := 0)
    (leakEnv loadExts : Bool) (level := OLeanLevel.private) (isModule := level != .private) :
    IO Environment := do
  let modules := s.moduleNames.filterMap (s.moduleNameMap[·]?)
  let moduleData ← modules.mapM fun mod => do
    let some data := mod.mainModule? |
      throw <| IO.userError s!"missing data file for module {mod.module}"
    return data
  let irData ← modules.mapM fun mod => do
    let some data := mod.interpData? level |
      throw <| IO.userError s!"missing IR data file for module {mod.module}"
    return data
  let numPrivateConsts := moduleData.foldl (init := 0) fun numPrivateConsts data =>
    numPrivateConsts + data.constants.size
  let numPrivateConsts := irData.foldl (init := numPrivateConsts) fun numPrivateConsts data =>
    numPrivateConsts + data.extraConstNames.size
  let numPublicConsts := modules.foldl (init := 0) fun numPublicConsts mod => Id.run do
    if !mod.isExported then numPublicConsts else
      let some data := mod.publicModule? | numPublicConsts
      numPublicConsts + data.constants.size
  let mut const2ModIdx : Std.HashMap Name ModuleIdx := Std.HashMap.emptyWithCapacity (capacity := numPrivateConsts + numPublicConsts)
  let mut privateConstantMap : Std.HashMap Name ConstantInfo := Std.HashMap.emptyWithCapacity (capacity := numPrivateConsts)
  let mut publicConstantMap : Std.HashMap Name ConstantInfo := Std.HashMap.emptyWithCapacity (capacity := numPublicConsts)
  for h : modIdx in *...moduleData.size do
    let data := moduleData[modIdx]
    for cname in data.constNames, cinfo in data.constants do
      match privateConstantMap.getThenInsertIfNew? cname cinfo with
      | (cinfoPrev?, constantMap') =>
        privateConstantMap := constantMap'
        if let some cinfoPrev := cinfoPrev? then
          -- Recall that the map has not been modified when `cinfoPrev? = some _`.
          if subsumesInfo privateConstantMap cinfo cinfoPrev then
            privateConstantMap := privateConstantMap.insert cname cinfo
          else if !subsumesInfo privateConstantMap cinfoPrev cinfo then
            throwAlreadyImported s const2ModIdx modIdx cname
      const2ModIdx := const2ModIdx.insertIfNew cname modIdx
    if let some data := irData[modIdx]? then
      for cname in data.extraConstNames do
        const2ModIdx := const2ModIdx.insertIfNew cname modIdx

  if isModule then
    for mod in modules.filter (·.isExported) do
      let some data := mod.publicModule? | continue
      for cname in data.constNames, cinfo in data.constants do
        match publicConstantMap.getThenInsertIfNew? cname cinfo with
        | (cinfoPrev?, constantMap') =>
          publicConstantMap := constantMap'
          if let some cinfoPrev := cinfoPrev? then
            if subsumesInfo publicConstantMap cinfo cinfoPrev then
              publicConstantMap := publicConstantMap.insert cname cinfo
            -- no need to check for duplicates again, `privateConstMap` should be a superset

  let exts ← mkInitialExtensionStates
  let privateConstants : ConstMap := SMap.fromHashMap privateConstantMap false
  let privateBase : Kernel.Environment := {
    const2ModIdx, constants := privateConstants
    quotInit        := !imports.isEmpty -- We assume `Init.Prelude` initializes quotient module
    extensions      := exts
    irBaseExts      := exts
    header     := {
      trustLevel, imports, moduleData, isModule
      modules      := modules.map (·.toEffectiveImport)
      regions      := modules.flatMap (·.parts.map (·.2)) ++ modules.filterMap (·.irData?.map (·.2))
    }
  }
  let publicConstants : ConstMap := SMap.fromHashMap publicConstantMap false
  let publicBase := { privateBase with constants := publicConstants, header.regions := #[] }
  let extensions ← setImportedEntries privateBase.extensions moduleData
  -- fall back to basic data when not in server
  let serverData := modules.mapIdx (fun idx mod => mod.serverData? level |>.getD moduleData[idx]!)
  let privateBase := { privateBase with
    extensions
    irBaseExts := (← setImportedEntries privateBase.extensions irData)
  }
  let mut env : Environment := {
    base.private := privateBase
    base.public  := publicBase
    importRealizationCtx? := none
    serverBaseExts := (← setImportedEntries privateBase.extensions serverData)
  }
  if leakEnv then
    /- Mark persistent a first time before `finalizePersistentExtensions`, which
       avoids costly MT markings when e.g. an interpreter closure (which
       contains the environment) is put in an `IO.Ref`. This can happen in e.g.
       initializers of user environment extensions and is wasteful because the
       environment is marked persistent immediately afterwards anyway when the
       constructed extension including the closure is ultimately stored in the
       initialized constant. We have seen significant savings in `open Mathlib`
       timings, where we have both a big environment and interpreted environment
       extensions, from this. There is no significant extra cost to calling
       `markPersistent` multiple times like this.

       Safety: There are no concurrent accesses to `env` at this point. -/
    env ← unsafe Runtime.markPersistent env
  if loadExts then
    env ← finalizePersistentExtensions env moduleData opts
    if leakEnv then
      /- Ensure the final environment including environment extension states is
        marked persistent as documented.

        Safety: There are no concurrent accesses to `env` at this point, assuming
        extensions' `addImportFn`s did not spawn any unbound tasks. -/
      env ← unsafe Runtime.markPersistent env
  return { env with importRealizationCtx? := some {
    -- safety: `RealizationContext` is private
    env := unsafe unsafeCast env
    opts
    realizeMapRef := (← IO.mkRef {})
  } }

/--
Creates environment object from given imports.

If `leakEnv` is true, we mark the environment as persistent, which means it will not be freed. We
set this when the object would survive until the end of the process anyway. In exchange, RC updates
are avoided, which is especially important when they would be atomic because the environment is
shared across threads (potentially, storing it in an `IO.Ref` is sufficient for marking it as such).

If `loadExts` is true, we initialize the environment extensions using the imported data. Doing so
may use the interpreter and thus is only safe to do after calling `enableInitializersExecution`; see
also caveats there. If not set, every extension will have its initial value as its state. While the
environment's constant map can be accessed without `loadExts`, many functions that take
`Environment` or are in a monad carrying it such as `CoreM` may not function properly without it.

If `level` is `exported`, the module to be elaborated is assumed to be participating in the module
system and imports will be restricted accordingly. If it is `server`, the data for
`getModuleEntries (includeServer := true)` is loaded as well. If it is `private`, all data is loaded
as if no `module` annotations were present in the imports.
-/
def importModules (imports : Array Import) (opts : Options) (trustLevel : UInt32 := 0)
    (plugins : Array System.FilePath := #[]) (leakEnv := false) (loadExts := false)
    (level := OLeanLevel.private) (arts : NameMap ImportArtifacts := {})
    : IO Environment := profileitIO "import" opts do
  for imp in imports do
    if imp.module matches .anonymous then
      throw <| IO.userError "import failed, trying to import module with anonymous name"
  withImporting do
    plugins.forM Lean.loadPlugin
    let (_, s) ← importModulesCore (globalLevel := level) imports arts |>.run
    finalizeImport (leakEnv := leakEnv) (loadExts := loadExts) (level := level)
      s imports opts trustLevel

/--
Creates environment object from imports and frees compacted regions after calling `act`. No live
references to the environment object or imported objects may exist after `act` finishes. As this
cannot be ruled out after loading environment extensions, `importModules`'s `loadExts` is always
unset using this function.
-/
unsafe def withImportModules {α : Type} (imports : Array Import) (opts : Options)
    (act : Environment → IO α) (trustLevel : UInt32 := 0) : IO α := do
  let env ← importModules (loadExts := false) imports opts trustLevel
  try act env finally env.freeRegions

@[inherit_doc Kernel.Environment.enableDiag]
def Kernel.enableDiag (env : Lean.Environment) (flag : Bool) : Lean.Environment :=
  env.modifyCheckedAsync (·.enableDiag flag)

def Kernel.isDiagnosticsEnabled (env : Lean.Environment) : Bool :=
  env.base.private.isDiagnosticsEnabled

def Kernel.resetDiag (env : Lean.Environment) : Lean.Environment :=
  env.modifyCheckedAsync (·.resetDiag)

def Kernel.getDiagnostics (env : Lean.Environment) : Diagnostics :=
  env.checked.get.diagnostics

def Kernel.setDiagnostics (env : Lean.Environment) (diag : Diagnostics) : Lean.Environment :=
  env.modifyCheckedAsync (·.setDiagnostics diag)

namespace Environment

@[export lean_elab_environment_update_base_after_kernel_add]
private def updateBaseAfterKernelAdd (env : Environment) (kenv : Kernel.Environment) (decl : Declaration) : Environment := {
    env with
    checked := .pure kenv
    -- HACK: the old codegen adds some helper constants directly to the kernel environment, we need
    -- to add them to the async consts as well in order to be able to replay them
    asyncConstsMap := env.asyncConstsMap.map fun asyncConsts =>
      decl.getNames.foldl (init := asyncConsts) fun asyncConsts n =>
        if looksLikeOldCodegenName n then
          asyncConsts.add {
            constInfo := .ofConstantInfo (kenv.find? n |>.get!)
            exts? := none
            aconstsImpl := .pure <| .mk (α := AsyncConsts) default
          }
        else asyncConsts
  }

def displayStats (env : Environment) : IO Unit := do
  let pExtDescrs ← persistentEnvExtensionsRef.get
  IO.println ("direct imports:                        " ++ toString env.header.imports);
  IO.println ("number of imported modules:            " ++ toString env.header.regions.size);
  IO.println ("number of memory-mapped modules:       " ++ toString (env.header.regions.filter (·.isMemoryMapped) |>.size));
  IO.println ("number of imported bytes:              " ++ toString (env.header.regions.map (·.size) |>.sum));
  IO.println ("number of imported consts:             " ++ toString env.constants.map₁.size);
  IO.println ("number of buckets for imported consts: " ++ toString env.constants.numBuckets);
  IO.println ("trust level:                           " ++ toString env.header.trustLevel);
  IO.println ("number of extensions:                  " ++ toString env.base.private.extensions.size);
  pExtDescrs.forM fun extDescr => do
    IO.println ("extension '" ++ toString extDescr.name ++ "'")
    -- get state from `checked` at the end if `async`; it would otherwise panic
    let mut asyncMode := extDescr.toEnvExtension.asyncMode
    if asyncMode matches .async _ then
      asyncMode := .sync
    let s := extDescr.toEnvExtension.getState (asyncMode := asyncMode) env
    let fmt := extDescr.statsFn s.state
    unless fmt.isNil do IO.println ("  " ++ toString (Format.nest 2 (extDescr.statsFn s.state)))
    IO.println ("  number of imported entries: " ++ toString (s.importedEntries.foldl (fun sum es => sum + es.size) 0))

@[extern "lean_eval_const"]
private unsafe opaque evalConstCore (α) (env : @& Environment) (opts : @& Options) (constName : @& Name) : Except String α

@[extern "lean_eval_check_meta"]
private opaque evalCheckMeta (env : Environment) (constName : Name) : Except String Unit

/--
Evaluates the given declaration under the given environment to a value of the given type.
This function is only safe to use if the type matches the declaration's type in the environment
and if `enableInitializersExecution` has been used before importing any modules.

If `checkMeta` is true (the default), the function checks that all referenced imported constants are
marked or imported as `meta` or otherwise fails with an error. It should only be set to `false` in
cases where it is acceptable for code to work only in the language server, where more IR is loaded,
such as in `#eval`.
-/
-- `[noinline]` helps with `prefer_native` so as to avoid trying to interpret the extern function
@[noinline] unsafe def evalConst (α) (env : @& Environment) (opts : @& Options) (constName : @& Name) (checkMeta := true) : Except String α := do
  if checkMeta then
    evalCheckMeta env constName
  evalConstCore α env opts constName

private def throwUnexpectedType {α} (typeName : Name) (constName : Name) : ExceptT String Id α :=
  throw ("unexpected type at '" ++ toString constName ++ "', `" ++ toString typeName ++ "` expected")

/--
Replays the difference between `newEnv` and `oldEnv` onto `dest`: the set of constants in `newEnv`
but not `oldEnv` and the environment extension state for extensions defining `replay?`. If
`skipExisting` is true, constants that are already in `dest` are not added. If `newEnv` and `dest`
are not derived from `oldEnv`, the result is undefined.
-/
def replayConsts (dest : Environment) (oldEnv newEnv : Environment) (skipExisting := false) :
    BaseIO Environment := do
  let numNewPrivateConsts := newEnv.asyncConstsMap.private.size - oldEnv.asyncConstsMap.private.size
  let newPrivateConsts := newEnv.asyncConstsMap.private.revList.take numNewPrivateConsts |>.reverse
  let numNewPublicConsts := newEnv.asyncConstsMap.public.size - oldEnv.asyncConstsMap.public.size
  let newPublicConsts := newEnv.asyncConstsMap.public.revList.take numNewPublicConsts |>.reverse
  let exts ← EnvExtension.envExtensionsRef.get
  return { dest with
    asyncConstsMap := {
      «private» := newPrivateConsts.foldl (init := dest.asyncConstsMap.private) fun consts c =>
        if skipExisting && (consts.find? c.constInfo.name).isSome then
          consts
        else
          consts.add c
      «public» := newPublicConsts.foldl (init := dest.asyncConstsMap.public) fun consts c =>
        if skipExisting && (consts.find? c.constInfo.name).isSome then
          consts
        else
          consts.add c
    }
    checked := dest.checked.map fun kenv =>
      replayKernel
        oldEnv.checked newEnv.checked exts newPrivateConsts kenv
      |>.toOption.getD kenv
    allRealizations := dest.allRealizations.map (sync := true) fun allRealizations =>
      newPrivateConsts.foldl (init := allRealizations) fun allRealizations c =>
        allRealizations.insert c.constInfo.name c
  }
where
  replayKernel (oldEnv newEnv : Task Kernel.Environment)
      (exts : Array (EnvExtension EnvExtensionState)) (consts : List AsyncConst)
      (kenv : Kernel.Environment) : Except Kernel.Exception Kernel.Environment := do
    let mut kenv := kenv
    -- replay extensions first in case kernel checking needs them (`IR.declMapExt`)
    for ext in exts do
      if let some replay := ext.replay? then
        kenv := { kenv with
          -- safety: like in `modifyState`, but that one takes an elab env instead of a kernel env
          extensions := unsafe (ext.modifyStateImpl kenv.extensions <|
            replay
              (ext.getStateImpl oldEnv.get.extensions)
              (ext.getStateImpl newEnv.get.extensions)
              (consts.map (·.constInfo.name))) }
    for c in consts do
      if skipExisting && (kenv.find? c.constInfo.name).isSome then
        continue
      let info := c.constInfo.toConstantInfo
      if info.isUnsafe then
        -- Checking unsafe declarations is not necessary for consistency, and it is necessary to
        -- avoid checking them in the case of the old code generator, which adds ill-typed constants
        -- to the kernel environment. We can delete this branch after removing the old code
        -- generator.
        kenv := kenv.add info
        continue
      -- for panics
      let _ : Inhabited Kernel.Environment := ⟨kenv⟩
      let decl ← match info with
        | .thmInfo thm   => pure <| .thmDecl thm
        | .defnInfo defn => pure <| .defnDecl defn
        | _              =>
          return panic! s!"{c.constInfo.name} must be definition/theorem"
      -- realized kernel additions cannot be interrupted - which would be bad anyway as they can be
      -- reused between snapshots
      kenv ← ofExcept <| kenv.addDeclCore 0 decl none
    return kenv

/-- Like `evalConst`, but first check that `constName` indeed is a declaration of type `typeName`.
    Note that this function cannot guarantee that `typeName` is in fact the name of the type `α`. -/
unsafe def evalConstCheck (α) (env : Environment) (opts : Options) (typeName : Name) (constName : Name) : ExceptT String Id α :=
  match env.find? constName with
  | none      => throw ("Unknown constant `" ++ toString constName ++ "`")
  | some info =>
    match info.type with
    | Expr.const c _ =>
      if c != typeName then throwUnexpectedType typeName constName
      else env.evalConst α opts constName
    | _ => throwUnexpectedType typeName constName

def hasUnsafe (env : Environment) (e : Expr) : Bool :=
  -- This line should not affect the result value but it avoids potential blocking in `isUnsafe` as
  -- there is a fast path for theorems, so we want to make sure we do not perceive them merely as
  -- axioms (for imported theorems this does not matter as there is nothing to block on).
  let env := env.setExporting false
  let c? := e.find? fun e => match e with
    | Expr.const c _ =>
      match env.findAsync? c with
      | some cinfo => cinfo.isUnsafe
      | none       => false
    | _ => false;
  c?.isSome

/-- Plumbing function for `Lean.Meta.realizeValue`; see documentation there. -/
def realizeValue [BEq α] [Hashable α] [TypeName α] (env : Environment) (forConst : Name) (key : α)
    (realize : Environment → Options → BaseIO Dynamic) : IO Dynamic := do
  -- the following code is inherently non-deterministic in number of heartbeats, reset them at the
  -- end
  let heartbeats ← IO.getNumHeartbeats
  -- find `RealizationContext` for `forConst` in `importRealizationCtx?` or `localRealizationCtxMap`
  let ctx ← if env.base.get env |>.const2ModIdx.contains forConst then
    env.importRealizationCtx?.getDM <|
      throw <| .userError s!"Environment.realizeConst: `realizedImportedConsts` is empty"
  else
    match env.localRealizationCtxMap.find? forConst with
    | some ctx => pure ctx
    | none =>
      throw <| .userError s!"trying to realize `{TypeName.typeName α}` value but \
        `enableRealizationsForConst` must be called for '{forConst}' first"
  let res ← (do
    -- First try checking for the key non-atomically as (de)allocating the promise is expensive.
    let m ← ctx.realizeMapRef.get
    if let some m' := m.find? (TypeName.typeName α) then
      -- Safety: `typeName α` should uniquely identify `PHashMap α (Task Dynamic)`; there are no other
      -- accesses to `private realizeMapRef` outside this function.
      let m' := unsafe unsafeCast (β := PHashMap α (Task Dynamic)) m'
      if let some t := m'[key] then
        return t.get

    -- Now check atomically.
    let prom ← IO.Promise.new
    let existingConsts? ← ctx.realizeMapRef.modifyGet fun m =>
      let m' := match m.find? (TypeName.typeName α) with
        | some m' => unsafe unsafeCast (β := PHashMap α (Task Dynamic)) m'
        | none    => {}
      match m'[key] with
      | some prom' => (some prom', m)
      | none =>
        let m' := m'.insert key prom.result!
        let m := m.insert (TypeName.typeName α) (unsafe unsafeCast (β := NonScalar) m')
        (none, m)
    if let some t := existingConsts? then
      pure t.get
    else
      -- safety: `RealizationContext` is private
      let realizeEnv : Environment := unsafe unsafeCast ctx.env
      let realizeEnv := { realizeEnv with
        -- allow realizations to recursively realize other constants for `forConst`. Do note that
        -- this allows for recursive realization of `α` itself, which will deadlock.
        localRealizationCtxMap := realizeEnv.localRealizationCtxMap.insert forConst ctx
        importRealizationCtx? := env.importRealizationCtx?
      }
      let res ← realize realizeEnv ctx.opts
      prom.resolve res
      pure res)
  IO.setNumHeartbeats heartbeats
  return res

private structure RealizeConstKey where
  constName : Name
deriving BEq, Hashable, TypeName

/-- Realization results, to be replayed onto other branches. -/
private structure RealizeConstResult where
  newConsts : VisibilityMap (List AsyncConst)
  replayKernel : Kernel.Environment → Except Kernel.Exception Kernel.Environment
  dyn : Dynamic
deriving Nonempty, TypeName

/-- Plumbing function for `Lean.Meta.realizeConst`; see documentation there. -/
def realizeConst (env : Environment) (forConst : Name) (constName : Name)
    (realize : Environment → Options → BaseIO (Environment × Dynamic)) :
    IO (Environment × Task (Option Kernel.Exception) × Dynamic) := do
  let res ← env.realizeValue forConst { constName : RealizeConstKey } fun realizeEnv realizeOpts => do
    -- ensure that environment extension modifications know they are in an async context
    let realizeEnv := realizeEnv.enterAsyncRealizing constName
    -- skip kernel in `realize`, we'll re-typecheck anyway
    let realizeOpts := debug.skipKernelTC.set realizeOpts true
    let (realizeEnv', dyn) ← realize realizeEnv realizeOpts
    -- We could check that `c` was indeed added here but in practice `realize` has already
    -- reported an error so we don't.

    -- find new constants incl. nested realizations, add current extension state, and compute
    -- closure
    let numNewPrivateConsts := realizeEnv'.asyncConstsMap.private.size - realizeEnv.asyncConstsMap.private.size
    let newPrivateConsts := realizeEnv'.asyncConstsMap.private.revList.take numNewPrivateConsts |>.reverse
    let newPrivateConsts := newPrivateConsts.map fun c =>
      let c := { c with isRealized := true }
      if c.exts?.isNone then
        { c with exts? := some <| .pure realizeEnv'.base.private.extensions }
      else c
    let numNewPublicConsts := realizeEnv'.asyncConstsMap.public.size - realizeEnv.asyncConstsMap.public.size
    let newPublicConsts := realizeEnv'.asyncConstsMap.public.revList.take numNewPublicConsts |>.reverse
    let newPublicConsts := newPublicConsts.map fun c =>
      let c := { c with isRealized := true }
      if c.exts?.isNone then
        { c with exts? := some <| .pure realizeEnv'.base.private.extensions }
      else c
    let exts ← EnvExtension.envExtensionsRef.get
    -- NOTE: We must ensure that `realizeEnv.localRealizationCtxMap` is not reachable via `res`
    -- (such as by storing `realizeEnv` or `realizeEnv'` in a field or the closure) as `res` will be
    -- stored in a promise in there, creating a cycle. The closures stored in
    -- `realizeEnv(').checked` should uphold this property as they are only concerned about the
    -- kernel env but this cannot directly be enforced or checked except through the leak sanitizer
    -- CI build.
    let replayKernel := replayConsts.replayKernel (skipExisting := true)
      realizeEnv.checked realizeEnv'.checked exts newPrivateConsts
    let res : RealizeConstResult := { newConsts.private := newPrivateConsts, newConsts.public := newPublicConsts, replayKernel, dyn }
    pure (.mk res)
  let some res := res.get? RealizeConstResult | unreachable!
  let exPromise ← IO.Promise.new
  let env := { env with
    asyncConstsMap := {
      «private» := res.newConsts.private.foldl (init := env.asyncConstsMap.private) fun consts c =>
        if consts.find? c.constInfo.name |>.isSome then
          consts
        else
          consts.add c
      «public»  := res.newConsts.public.foldl (init := env.asyncConstsMap.public) fun consts c =>
        if consts.find? c.constInfo.name |>.isSome then
          consts
        else
          consts.add c
    }
    checked := (← BaseIO.mapTask (t := env.checked) fun kenv => do
      match res.replayKernel kenv with
      | .ok kenv => return kenv
      | .error e =>
        exPromise.resolve e
        return kenv)
    allRealizations := env.allRealizations.map (sync := true) fun allRealizations =>
      res.newConsts.private.foldl (init := allRealizations) fun allRealizations c =>
        allRealizations.insert c.constInfo.name c
  }
  return (env, exPromise.result?, res.dyn)

end Environment

namespace Kernel
/-! # Kernel API -/

/--
  Kernel isDefEq predicate. We use it mainly for debugging purposes.
  Recall that the kernel type checker does not support metavariables.
  When implementing automation, consider using the `MetaM` methods. -/
-- We use `Lean.Environment` for ease of use; as this is a debugging function, we forgo a
-- `Kernel.Environment` base variant
@[extern "lean_kernel_is_def_eq"]
opaque isDefEq (env : Lean.Environment) (lctx : LocalContext) (a b : Expr) : Except Kernel.Exception Bool

def isDefEqGuarded (env : Lean.Environment) (lctx : LocalContext) (a b : Expr) : Bool :=
  if let .ok result := isDefEq env lctx a b then result else false

/--
  Kernel WHNF function. We use it mainly for debugging purposes.
  Recall that the kernel type checker does not support metavariables.
  When implementing automation, consider using the `MetaM` methods. -/
-- We use `Lean.Environment` for ease of use; as this is a debugging function, we forgo a
-- `Kernel.Environment` base variant
@[extern "lean_kernel_whnf"]
opaque whnf (env : Lean.Environment) (lctx : LocalContext) (a : Expr) : Except Kernel.Exception Expr

/--
  Kernel typecheck function. We use it mainly for debugging purposes.
  Recall that the Kernel type checker does not support metavariables.
  When implementing automation, consider using the `MetaM` methods. -/
-- We use `Lean.Environment` for ease of use; as this is a debugging function, we forgo a
-- `Kernel.Environment` base variant
@[extern "lean_kernel_check"]
opaque check (env : Lean.Environment) (lctx : LocalContext) (a : Expr) : Except Kernel.Exception Expr

end Kernel

class MonadEnv (m : Type → Type) where
  getEnv    : m Environment
  modifyEnv : (Environment → Environment) → m Unit

export MonadEnv (getEnv modifyEnv)

/-- Returns the module name of the current file. -/
def getMainModule [Monad m] [MonadEnv m] : m Name :=
  return (← getEnv).header.mainModule

@[always_inline]
instance (m n) [MonadLift m n] [MonadEnv m] : MonadEnv n where
  getEnv    := liftM (getEnv : m Environment)
  modifyEnv := fun f => liftM (modifyEnv f : m Unit)

/--
Sets `Environment.isExporting` to the given value while executing `x`. No-op if
`EnvironmentHeader.isModule` is false.
-/
def withExporting [Monad m] [MonadEnv m] [MonadFinally m] [MonadOptions m] (x : m α)
    (isExporting := true) : m α := do
  let old := (← getEnv).isExporting
  modifyEnv (·.setExporting isExporting)
  try
    x
  finally
    modifyEnv (·.setExporting old)

/-- If `when` is true, sets `Environment.isExporting` to false while executing `x`. -/
def withoutExporting [Monad m] [MonadEnv m] [MonadFinally m] [MonadOptions m] (x : m α)
    (when : Bool := true) : m α :=
  if when then
    withExporting (isExporting := false) x
  else
    x

/-- Constructs a DefinitionVal, inferring the `unsafe` field -/
def mkDefinitionValInferringUnsafe [Monad m] [MonadEnv m] (name : Name) (levelParams : List Name)
    (type : Expr) (value : Expr) (hints : ReducibilityHints) : m DefinitionVal := do
  let env ← getEnv
  let safety := if env.hasUnsafe type || env.hasUnsafe value then DefinitionSafety.unsafe else DefinitionSafety.safe
  return { name, levelParams, type, value, hints, safety }

/-- Constructs a declaration from a theorem, resorting to an unsafe def if needed -/
def mkThmOrUnsafeDef [Monad m] [MonadEnv m] (thm : TheoremVal) : m Declaration := do
  let env ← getEnv
  if env.hasUnsafe thm.type || env.hasUnsafe thm.value then
    return .defnDecl { thm with safety := DefinitionSafety.unsafe, hints := .opaque }
  else
    return .thmDecl thm

def getMaxHeight (env : Environment) (e : Expr) : UInt32 :=
  e.foldConsts 0 fun constName max =>
    match env.findAsync? constName with
    | some { kind := .defn, constInfo := info, .. } =>
      match info.get.hints with
      | ReducibilityHints.regular h => if h > max then h else max
      | _                           => max
    | _ => max

end Lean
