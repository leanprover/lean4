/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Control.StateRef
import Init.Data.Array.BinSearch
import Init.Data.Stream
import Init.System.Promise
import Lean.ImportingFlag
import Lean.Data.HashMap
import Lean.Data.NameTrie
import Lean.Data.SMap
import Lean.Declaration
import Lean.LocalContext
import Lean.Util.Path
import Lean.Util.FindExpr
import Lean.Util.Profile
import Lean.Util.InstantiateLevelParams
import Lean.Util.FoldConsts
import Lean.PrivateName
import Lean.LoadDynlib
import Init.Dynamic

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
  group    := "debug"
  descr    := "skip kernel type checker. WARNING: setting this option to true may compromise soundness because your proofs will not be checked by the Lean kernel"
}

/-- Opaque environment extension state. -/
opaque EnvExtensionStateSpec : (α : Type) × Inhabited α := ⟨Unit, ⟨()⟩⟩
def EnvExtensionState : Type := EnvExtensionStateSpec.fst
instance : Inhabited EnvExtensionState := EnvExtensionStateSpec.snd

def ModuleIdx := Nat
  deriving BEq, ToString

abbrev ModuleIdx.toNat (midx : ModuleIdx) : Nat := midx

instance : Inhabited ModuleIdx where default := (0 : Nat)

instance : GetElem (Array α) ModuleIdx α (fun a i => i.toNat < a.size) where
  getElem a i h := a[i.toNat]

instance : GetElem? (Array α) ModuleIdx α (fun a i => i.toNat < a.size) where
  getElem? a i := a[i.toNat]?
  getElem! a i := a[i.toNat]!

abbrev ConstMap := SMap Name ConstantInfo

structure Import where
  module      : Name
  runtimeOnly : Bool := false
  deriving Repr, Inhabited

instance : Coe Name Import := ⟨({module := ·})⟩

instance : ToString Import := ⟨fun imp => toString imp.module ++ if imp.runtimeOnly then " (runtime)" else ""⟩

/--
  A compacted region holds multiple Lean objects in a contiguous memory region, which can be read/written to/from disk.
  Objects inside the region do not have reference counters and cannot be freed individually. The contents of .olean
  files are compacted regions. -/
def CompactedRegion := USize

@[extern "lean_compacted_region_is_memory_mapped"]
opaque CompactedRegion.isMemoryMapped : CompactedRegion → Bool

/-- Free a compacted region and its contents. No live references to the contents may exist at the time of invocation. -/
@[extern "lean_compacted_region_free"]
unsafe opaque CompactedRegion.free : CompactedRegion → IO Unit

/-- Opaque persistent environment extension entry. -/
opaque EnvExtensionEntrySpec : NonemptyType.{0}
def EnvExtensionEntry : Type := EnvExtensionEntrySpec.type
instance : Nonempty EnvExtensionEntry := EnvExtensionEntrySpec.property

/-- Content of a .olean file.
   We use `compact.cpp` to generate the image of this object in disk. -/
structure ModuleData where
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
  /-- Direct imports -/
  imports      : Array Import := #[]
  /-- Compacted regions for all imported modules. Objects in compacted memory regions do no require any memory management. -/
  regions      : Array CompactedRegion := #[]
  /--
  Name of all imported modules (directly and indirectly).
  The index of a module name in the array equals the `ModuleIdx` for the same module.
  -/
  moduleNames  : Array Name   := #[]
  /-- Module data for all imported modules. -/
  moduleData   : Array ModuleData := #[]
  deriving Nonempty

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
  Constant names to be saved in the field `extraConstNames` at `ModuleData`.
  It contains auxiliary declaration names created by the code generator which are not in `constants`.
  When importing modules, we want to insert them at `const2ModIdx`.
  -/
  private extraConstNames : NameSet
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

/-- Basic `Exception` formatting without `MessageData` dependency. -/
private def Exception.toRawString : Kernel.Exception → String
  | unknownConstant _ constName       => s!"(kernel) unknown constant '{constName}'"
  | alreadyDeclared _ constName       => s!"(kernel) constant has already been declared '{constName}'"
  | declTypeMismatch _ _ _ => s!"(kernel) declaration type mismatch"
  | declHasMVars _ constName _        => s!"(kernel) declaration has metavariables '{constName}'"
  | declHasFVars _ constName _        => s!"(kernel) declaration has free variables '{constName}'"
  | funExpected _ _ e                 => s!"(kernel) function expected: {e}"
  | typeExpected _ _ e                => s!"(kernel) type expected: {e}"
  | letTypeMismatch  _ _ n _ _        => s!"(kernel) let-declaration type mismatch '{n}'"
  | exprTypeMismatch _ _ e _          => s!"(kernel) type mismatch at {e}"
  | appTypeMismatch  _ _ e fnType argType =>
    s!"application type mismatch: {e}\nargument has type {argType}\nbut function has type {fnType}"
  | invalidProj _ _ e                 => s!"(kernel) invalid projection {e}"
  | thmTypeIsNotProp _ constName type => s!"(kernel) type of theorem '{constName}' is not a proposition: {type}"
  | other msg                         => s!"(kernel) {msg}"
  | deterministicTimeout              => "(kernel) deterministic timeout"
  | excessiveMemory                   => "(kernel) excessive memory consumption detected"
  | deepRecursion                     => "(kernel) deep recursion detected"
  | interrupted                       => "(kernel) interrupted"

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

@[deprecated Kernel.Exception (since := "2024-12-12")]
abbrev KernelException := Kernel.Exception

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
  /-- Whether we are in `realizeConst`, used to restrict env ext modifications. -/
  realizing  : Bool
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
  constInfo : AsyncConstantInfo
  /--
  Reported extension state eventually fulfilled by promise; may be missing for tasks (e.g. kernel
  checking) that can eagerly guarantee they will not report any state.
  -/
  exts?     : Option (Task (Array EnvExtensionState))
  /--
  `Task AsyncConsts` except for problematic recursion. The set of nested constants created while
  elaborating this constant.
  -/
  consts    : Task Dynamic

/-- Data structure holding a sequence of `AsyncConst`s optimized for efficient access. -/
private structure AsyncConsts where
  size : Nat
  revList : List AsyncConst
  /-- Map from declaration name to const for fast direct access. -/
  map : NameMap AsyncConst
  /-- Trie of declaration names without private name prefixes for fast longest-prefix access. -/
  normalizedTrie : NameTrie AsyncConst
deriving Inhabited, TypeName

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
Finds constants including from other elaboration branches by recursively looking up longest
prefixes (which is sufficient by `AsyncContext.mayContain`).
-/
private partial def AsyncConsts.findRec? (aconsts : AsyncConsts) (declName : Name) : Option AsyncConst := do
  let c ← aconsts.findPrefix? declName
  if c.constInfo.name == declName then
    return c
  let aconsts ← c.consts.get.get? AsyncConsts
  AsyncConsts.findRec? aconsts declName

/-- Context for `realizeConst` established by `enableRealizationsForConst`. -/
private structure RealizationContext where
  /--
  Saved `Environment`, untyped to avoid cyclic reference. Import environment for imported constants.
  -/
  env       : NonScalar
  /-- Saved options. Empty for imported constants. -/
  opts      : Options
  /--
  `realizeConst _ c ..` adds a mapping from `c` to a task of the realization results: the newly
  added constants (incl. extension data in `AsyncConst.exts?`),  a function for replaying the
  changes onto a derived kernel environment, and auxiliary data (always `SnapshotTree` in builtin
  uses, but untyped to avoid cyclic module references).
  -/
  constsRef : IO.Ref (NameMap (Task (List AsyncConst × (Kernel.Environment → Kernel.Environment) × Dynamic)))

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
  Kernel environment containing imported constants. Also stores environment extension state for the
  current branch of the environment.

  As `base` is eagerly available, we prefer taking information from it instead of `checked` whenever
  possible.
  -/
  base : Kernel.Environment
  /--
  Kernel environment task that is fulfilled when all asynchronously elaborated declarations are
  finished, containing the resulting environment. Also collects the environment extension state of
  all environment branches that contributed contained declarations.
  -/
  checked             : Task Kernel.Environment := .pure base
  /--
  Container of asynchronously elaborated declarations. For consistency, `updateBaseAfterKernelAdd`
  makes sure this contains constants added even synchronously, i.e. `base ⨃ asyncConsts` is the set
  of constants known on the current environment branch, which is a subset of `checked`.
  -/
  private asyncConsts : AsyncConsts := default
  /-- Information about this asynchronous branch of the environment, if any. -/
  private asyncCtx?   : Option AsyncContext := none
  /--
  Realized constants belonging to imported declarations. Must be initialized by calling
  `enableRealizationsForImports`.
  -/
  private realizedImportedConsts? : Option RealizationContext
  /--
  Realized constants belonging to local declarations. This is a map from local declarations, which
  need to be registered synchronously using `enableRealizationsForConst`, to their realization
  context incl. a ref of realized constants.
  -/
  private realizedLocalConsts  : NameMap RealizationContext := {}
deriving Nonempty

namespace Environment

-- used only when the kernel calls into the interpreter, and in `Lean.Kernel.Exception.mkCtx`
@[export lean_elab_environment_of_kernel_env]
def ofKernelEnv (env : Kernel.Environment) : Environment :=
  { base := env, realizedImportedConsts? := none }

@[export lean_elab_environment_to_kernel_env]
def toKernelEnv (env : Environment) : Kernel.Environment :=
  env.checked.get

/-- Consistently updates synchronous and asynchronous parts of the environment without blocking. -/
private def modifyCheckedAsync (env : Environment) (f : Kernel.Environment → Kernel.Environment) : Environment :=
  { env with checked := env.checked.map (sync := true) f, base := f env.base }

/-- Sets synchronous and asynchronous parts of the environment to the given kernel environment. -/
private def setCheckedSync (env : Environment) (newChecked : Kernel.Environment) : Environment :=
  { env with checked := .pure newChecked, base := newChecked }

/-- The declaration prefix to which the environment is restricted to, if any. -/
def asyncPrefix? (env : Environment) : Option Name :=
  env.asyncCtx?.map (·.declPrefix)

/-- True while inside `realizeConst`'s `realize`. -/
def isRealizing (env : Environment) : Bool :=
  env.asyncCtx?.any (·.realizing)

/-- Forgets about the asynchronous context restrictions. Used only for `withoutModifyingEnv`. -/
def unlockAsync (env : Environment) : Environment :=
  { env with asyncCtx? := none }

/--
Checks whether the given declaration name may potentially added, or have been added, to the current
environment branch, which is the case either if this is the main branch or if the declaration name
is a suffix (modulo privacy and hygiene information) of the top-level declaration name for which
this branch was created.

This function should always be checked before modifying an `AsyncMode.async` environment extension
to ensure `findStateAsync` will be able to find the modification from other branches.
-/
def asyncMayContain (env : Environment) (declName : Name) : Bool :=
  env.asyncCtx?.all (·.mayContain declName)

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
  if doCheck then
    addDeclCheck env maxHeartbeats decl cancelTk?
  else
    addDeclWithoutChecking env decl

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
  { env with asyncConsts := env.asyncConsts.add {
    constInfo := .ofConstantInfo cinfo
    exts? := none
    consts := .pure <| .mk (α := AsyncConsts) default
  } }

/--
Save an extra constant name that is used to populate `const2ModIdx` when we import
.olean files. We use this feature to save in which module an auxiliary declaration
created by the code generator has been created.
-/
def addExtraName (env : Environment) (name : Name) : Environment :=
  if env.constants.contains name then
    env
  else
    env.modifyCheckedAsync fun env => { env with extraConstNames := env.extraConstNames.insert name }

/-- `findAsync?` after `base` access -/
private def findAsyncCore? (env : Environment) (n : Name) : Option AsyncConstantInfo := do
  if let some asyncConst := env.asyncConsts.find? n then
    -- Constant for which an asynchronous elaboration task was spawned
    return asyncConst.constInfo
  if let some c := env.asyncConsts.findRec? n then
    -- Constant generated in a different environment branch
    return c.constInfo
  -- Not in the kernel environment nor in the name prefix of a known environment branch: undefined
  -- by `addDeclCore` invariant.
  none

/--
Looks up the given declaration name in the environment, avoiding forcing any in-progress elaboration
tasks unless necessary.
-/
def findAsync? (env : Environment) (n : Name) : Option AsyncConstantInfo := do
  -- Avoid going through `AsyncConstantInfo` for `base` access
  if let some c := env.base.constants.map₁[n]? then
    return .ofConstantInfo c
  findAsyncCore? env n

/--
Looks up the given declaration name in the environment, avoiding forcing any in-progress elaboration
tasks for declaration bodies (which are not accessible from `ConstantVal`).
-/
def findConstVal? (env : Environment) (n : Name) : Option ConstantVal := do
  -- Avoid going through `AsyncConstantInfo` for `base` access
  if let some c := env.base.constants.map₁[n]? then
    return c.toConstantVal
  env.findAsyncCore? n |>.map (·.toConstantVal)

/--
Allows `realizeConst` calls for imported declarations in all derived environment branches.
Realizations will run using the given environment and options to ensure deterministic results.
This function should be called directly after `setMainModule` to ensure that all realized constants
use consistent private prefixes.
-/
def enableRealizationsForImports (env : Environment) (opts : Options) : BaseIO Environment :=
  return { env with realizedImportedConsts? := some {
      -- safety: `RealizationContext` is private
      env := unsafe unsafeCast env
      opts
      constsRef := (← IO.mkRef {})
    }
  }

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
  if env.findAsync? c |>.isNone then
    panic! s!"declaration {c} not found in environment"
    return env
  if let some asyncCtx := env.asyncCtx? then
    if !asyncCtx.mayContain c then
      panic! s!"{c} is outside current context {asyncCtx.declPrefix}"
      return env
  if env.realizedLocalConsts.contains c then
    return env
  return { env with realizedLocalConsts := env.realizedLocalConsts.insert c {
    -- safety: `RealizationContext` is private
    env := unsafe unsafeCast env
    opts
    constsRef := (← IO.mkRef {}) } }

/--
Looks up the given declaration name in the environment, blocking on the corresponding elaboration
task if not yet complete.
-/
def find? (env : Environment) (n : Name) : Option ConstantInfo := do
  if let some c := env.base.constants.map₁[n]? then
    return c
  env.findAsyncCore? n |>.map (·.toConstantInfo)

/-- Returns debug output about the asynchronous state of the environment. -/
def dbgFormatAsyncState (env : Environment) : BaseIO String :=
  return s!"\
    asyncCtx.declPrefix: {repr <| env.asyncCtx?.map (·.declPrefix)}\
  \nasyncConsts: {repr <| env.asyncConsts.revList.reverse.map (·.constInfo.name)}\
  \nrealizedLocalConsts: {repr (← env.realizedLocalConsts.toList.mapM fun (n, ctx) => do
    let consts := (← ctx.constsRef.get).toList
    return (n, consts.map (·.1)))}
  \nrealizedImportedConsts?: {repr <| (← env.realizedImportedConsts?.mapM fun ctx => do
    return (← ctx.constsRef.get).toList.map fun (n, m?) =>
      (n, m?.get.1.map (fun c : AsyncConst => c.constInfo.name.toString) |> toString))}
  \nbase.constants.map₂: {repr <| env.base.constants.map₂.toList.map (·.1)}"

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

/-- Creates an async context for the given declaration name, normalizing it for use as a prefix. -/
private def enterAsync (declName : Name) (realizing := false) (env : Environment) : Environment :=
  { env with asyncCtx? := some {
    declPrefix := privateToUserName declName.eraseMacroScopes
    -- `realizing` is sticky
    realizing := realizing || env.asyncCtx?.any (·.realizing) } }

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
  private sigPromise : IO.Promise ConstantVal
  private infoPromise : IO.Promise ConstantInfo
  private extensionsPromise : IO.Promise (Array EnvExtensionState)
  private checkedEnvPromise : IO.Promise Kernel.Environment
  private constsPromise : IO.Promise AsyncConsts

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
-/
def addConstAsync (env : Environment) (constName : Name) (kind : ConstantKind) (reportExts := true)
    (checkMayContain := true) :
    IO AddConstAsyncResult := do
  if checkMayContain then
    if let some ctx := env.asyncCtx? then
      if !ctx.mayContain constName then
        throw <| .userError s!"cannot add declaration {constName} to environment as it is \
          restricted to the prefix {ctx.declPrefix}"
  let sigPromise ← IO.Promise.new
  let infoPromise ← IO.Promise.new
  let extensionsPromise ← IO.Promise.new
  let checkedEnvPromise ← IO.Promise.new
  let constsPromise ← IO.Promise.new

  -- We use a thunk here because we don't have a fallback for recursors, but that specific
  -- invocation cannot fail anyway
  let fallbackConstInfo := Thunk.mk fun _ => mkFallbackConstInfo constName kind

  let asyncConst := {
    constInfo := {
      name := constName
      kind
      sig := sigPromise.resultD fallbackConstInfo.get.toConstantVal
      constInfo := infoPromise.resultD fallbackConstInfo.get
    }
    exts? := guard reportExts *> some (extensionsPromise.resultD env.toKernelEnv.extensions)
    consts := constsPromise.result?.map (sync := true) fun
      | some consts => .mk consts
      | none        => .mk (α := AsyncConsts) default
  }
  return {
    constName, kind
    mainEnv := { env with
      asyncConsts := env.asyncConsts.add asyncConst
      checked := checkedEnvPromise.result?.bind (sync := true) fun
        | some kenv => .pure kenv
        | none      => env.checked }
    asyncEnv := env.enterAsync constName
    sigPromise, infoPromise, extensionsPromise, checkedEnvPromise, constsPromise
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
    (info? : Option ConstantInfo := none) :
    IO Unit := do
  let info ← match info? <|> env.find? res.constName with
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
  res.infoPromise.resolve info
  res.extensionsPromise.resolve env.base.extensions
  res.constsPromise.resolve env.asyncConsts

/--
Assuming `Lean.addDecl` has been run for the constant to be added on the async environment branch,
commits the full constant info from that call to the main environment, waits for the final kernel
environment resulting from the `addDecl` call, and commits it to the main branch as well, unblocking
kernel additions there. All `commitConst` preconditions apply.
-/
def AddConstAsyncResult.commitCheckEnv (res : AddConstAsyncResult) (env : Environment) :
    IO Unit := do
  -- We should skip `commitConst` in case it has already been called, perhaps with a different
  -- `info?`
  if !(← res.infoPromise.isResolved) then
    res.commitConst env
  res.checkedEnvPromise.resolve env.checked.get

def contains (env : Environment) (n : Name) : Bool :=
  env.findAsync? n |>.isSome

/--
Checks whether the given declaration is known on the current branch, in which case `findAsync?` will
not block.
-/
def containsOnBranch (env : Environment) (n : Name) : Bool :=
  (env.asyncConsts.find? n |>.isSome) || env.base.constants.contains n

def header (env : Environment) : EnvironmentHeader :=
  -- can be assumed to be in sync with `env.checked`; see `setMainModule`, the only modifier of the header
  env.base.header

def imports (env : Environment) : Array Import :=
  env.header.imports

def allImportedModuleNames (env : Environment) : Array Name :=
  env.header.moduleNames

def setMainModule (env : Environment) (m : Name) : Environment := Id.run do
  if env.realizedImportedConsts?.isSome then
    let _ : Inhabited Environment := ⟨env⟩
    return panic! "cannot set after `enableRealizationsForImports`"
  env.modifyCheckedAsync ({ · with header.mainModule := m })

def mainModule (env : Environment) : Name :=
  env.header.mainModule

def getModuleIdxFor? (env : Environment) (declName : Name) : Option ModuleIdx :=
  -- async constants are always from the current module
  env.base.const2ModIdx[declName]?

def isConstructor (env : Environment) (declName : Name) : Bool :=
  match env.find? declName with
  | some (.ctorInfo _) => true
  | _                  => false

def isSafeDefinition (env : Environment) (declName : Name) : Bool :=
  match env.find? declName with
  | some (.defnInfo { safety := .safe, .. }) => true
  | _ => false

def getModuleIdx? (env : Environment) (moduleName : Name) : Option ModuleIdx :=
  env.header.moduleNames.findIdx? (· == moduleName)

end Environment

namespace ConstantInfo

def instantiateTypeLevelParams (c : ConstantInfo) (ls : List Level) : Expr :=
  c.type.instantiateLevelParams c.levelParams ls

def instantiateValueLevelParams! (c : ConstantInfo) (ls : List Level) : Expr :=
  c.value!.instantiateLevelParams c.levelParams ls

end ConstantInfo

/--
Async access mode for environment extensions used in `EnvironmentExtension.get/set/modifyState`.
Depending on their specific uses, extensions may opt out of the strict `sync` access mode in order
to avoid blocking parallel elaboration and/or to optimize accesses. The access mode is set at
environment extension registration time but can be overriden at `EnvironmentExtension.getState` in
order to weaken it for specific accesses.

In all modes, the state stored into the `.olean` file for persistent environment extensions is the
result of `getState` called on the main environment branch at the end of the file, i.e. it
encompasses all modifications for all modes but `local`.
-/
inductive EnvExtension.AsyncMode where
  /--
  Default access mode, writing and reading the extension state to/from the full `checked`
  environment. This mode ensures the observed state is identical independently of whether or how
  parallel elaboration is used but `getState` will block on all prior environment branches by
  waiting for `checked`. `setState` and `modifyState` do not block.

  While a safe default, any extension that reasonably could be used in parallel elaboration contexts
  should opt for a weaker mode to avoid blocking unless there is no way to access the correct state
  without waiting for all prior environment branches, in which case its data management should be
  restructured if at all possible.
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
  Like `local` but panics when trying to modify the state on anything but the main environment
  branch. For extensions that fulfill this requirement, all modes functionally coincide but this
  is the safest and most efficient choice in that case, preventing accidental misuse.

  This mode is suitable for extensions that are modified only at the command elaboration level
  before any environment forks in the command, and in particular for extensions that are modified
  only at the very beginning of the file.
  -/
  | mainOnly
  /--
  Accumulates modifications in the `checked` environment like `sync`, but `getState` will panic
  instead of blocking. Instead `findStateAsync` should be used, which will access the state of the
  environment branch corresponding to the passed declaration name, if any, or otherwise the state
  of the current branch. In other words, at most one environment branch will be blocked on instead
  of all prior branches. The local state can still be accessed by calling `getState` with mode
  `local` explicitly.

  This mode is suitable for extensions with map-like state where the key uniquely identifies the
  top-level declaration where it could have been set, e.g. because the key on modification is always
  the surrounding declaration's name. Any calls to `modifyState`/`setState` should assert
  `asyncMayContain` with that key to ensure state is never accidentally stored in a branch where it
  cannot be found by `findStateAsync`. In particular, this mode is closest to how the environment's
  own constant map works which asserts the same predicate on modification and provides `findAsync?`
  for block-avoiding access.
  -/
  | async
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
Applies the given function to the extension state. See `AsyncMode` for details on how modifications
from different environment branches are reconciled.

Note that in modes `sync` and `async`, `f` will be called twice, on the local and on the `checked`
state.
-/
def modifyState {σ : Type} (ext : EnvExtension σ) (env : Environment) (f : σ → σ) : Environment := Id.run do
  -- for panics
  let _ : Inhabited Environment := ⟨env⟩
  -- safety: `ext`'s constructor is private, so we can assume the entry at `ext.idx` is of type `σ`
  match ext.asyncMode with
  | .mainOnly =>
    if let some asyncCtx := env.asyncCtx? then
      return panic! s!"environment extension is marked as `mainOnly` but used in \
        {if asyncCtx.realizing then "realization" else "async"} context '{asyncCtx.declPrefix}'"
    return { env with base.extensions := unsafe ext.modifyStateImpl env.base.extensions f }
  | .local =>
    return { env with base.extensions := unsafe ext.modifyStateImpl env.base.extensions f }
  | _ =>
    if ext.replay?.isNone then
      if let some asyncCtx := env.asyncCtx?.filter (·.realizing) then
        return panic! s!"environment extension must set `replay?` field to be \
          used in realization context '{asyncCtx.declPrefix}'"
    env.modifyCheckedAsync fun env =>
      { env with extensions := unsafe ext.modifyStateImpl env.extensions f }

/--
Sets the extension state to the given value. See `AsyncMode` for details on how modifications from
different environment branches are reconciled.
-/
def setState {σ : Type} (ext : EnvExtension σ) (env : Environment) (s : σ) : Environment :=
  inline <| modifyState ext env fun _ => s

-- `unsafe` fails to infer `Nonempty` here
private unsafe def getStateUnsafe {σ : Type} [Inhabited σ] (ext : EnvExtension σ)
    (env : Environment) (asyncMode := ext.asyncMode) : σ :=
  -- safety: `ext`'s constructor is private, so we can assume the entry at `ext.idx` is of type `σ`
  match asyncMode with
  | .sync     => ext.getStateImpl env.checked.get.extensions
  | .async    => panic! "called on `async` extension, use `findStateAsync` \
    instead or pass `(asyncMode := .local)` to explicitly access local state"
  | _         => ext.getStateImpl env.base.extensions

/--
Returns the current extension state. See `AsyncMode` for details on how modifications from
different environment branches are reconciled. Panics if the extension is marked as `async`; see its
documentation for more details. Overriding the extension's default `AsyncMode` is usually not
recommended and should be considered only for important optimizations.
-/
@[implemented_by getStateUnsafe]
opaque getState {σ : Type} [Inhabited σ] (ext : EnvExtension σ) (env : Environment)
  (asyncMode := ext.asyncMode) : σ

-- `unsafe` fails to infer `Nonempty` here
private unsafe def findStateAsyncUnsafe {σ : Type} [Inhabited σ]
    (ext : EnvExtension σ) (env : Environment) (declPrefix : Name) : σ :=
  -- safety: `ext`'s constructor is private, so we can assume the entry at `ext.idx` is of type `σ`
  if let some { exts? := some exts, .. } := env.asyncConsts.findRec? declPrefix then
    ext.getStateImpl exts.get
  else
    ext.getStateImpl env.base.extensions

/--
Returns the final extension state on the environment branch corresponding to the passed declaration
name, if any, or otherwise the state on the current branch. In other words, at most one environment
branch will be blocked on.
-/
@[implemented_by findStateAsyncUnsafe]
opaque findStateAsync {σ : Type} [Inhabited σ] (ext : EnvExtension σ)
  (env : Environment) (declPrefix : Name) : σ

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
    base := {
      const2ModIdx    := {}
      constants       := {}
      header          := { trustLevel }
      extraConstNames := {}
      extensions      := exts
    }
    realizedImportedConsts? := none
  }

structure PersistentEnvExtensionState (α : Type) (σ : Type) where
  importedEntries : Array (Array α)  -- entries per imported module
  state : σ

structure ImportM.Context where
  env  : Environment
  opts : Options

abbrev ImportM := ReaderT Lean.ImportM.Context IO

/--
An environment extension with support for storing/retrieving entries from a .olean file.
 - α is the type of the entries that are stored in .olean files.
 - β is the type of values used to update the state.
 - σ is the actual state.

For most extensions, α and β coincide. `α` and ‵β` do not coincide for extensions where the data
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
  exportEntriesFn : σ → Array α
  statsFn         : σ → Format

instance {α σ} [Inhabited σ] : Inhabited (PersistentEnvExtensionState α σ) :=
  ⟨{importedEntries := #[], state := default }⟩

instance {α β σ} [Inhabited σ] : Inhabited (PersistentEnvExtension α β σ) where
  default := {
     toEnvExtension := default,
     name := default,
     addImportedFn := fun _ => default,
     addEntryFn := fun s _ => s,
     exportEntriesFn := fun _ => #[],
     statsFn := fun _ => Format.nil
  }

namespace PersistentEnvExtension

def getModuleEntries {α β σ : Type} [Inhabited σ] (ext : PersistentEnvExtension α β σ) (env : Environment) (m : ModuleIdx) : Array α :=
  -- `importedEntries` is identical on all environment branches, so `local` is always sufficient
  (ext.toEnvExtension.getState (asyncMode := .local) env).importedEntries[m]!

def addEntry {α β σ : Type} (ext : PersistentEnvExtension α β σ) (env : Environment) (b : β) : Environment :=
  ext.toEnvExtension.modifyState env fun s =>
    let state   := ext.addEntryFn s.state b;
    { s with state := state }

/-- Get the current state of the given extension in the given environment. -/
def getState {α β σ : Type} [Inhabited σ] (ext : PersistentEnvExtension α β σ) (env : Environment)
    (asyncMode := ext.toEnvExtension.asyncMode) : σ :=
  (ext.toEnvExtension.getState (asyncMode := asyncMode) env).state

/-- Set the current state of the given extension in the given environment. -/
def setState {α β σ : Type} (ext : PersistentEnvExtension α β σ) (env : Environment) (s : σ) : Environment :=
  ext.toEnvExtension.modifyState env fun ps => { ps with  state := s }

/-- Modify the state of the given extension in the given environment by applying the given function. -/
def modifyState {α β σ : Type} (ext : PersistentEnvExtension α β σ) (env : Environment) (f : σ → σ) : Environment :=
  ext.toEnvExtension.modifyState env fun ps => { ps with state := f (ps.state) }

@[inherit_doc EnvExtension.findStateAsync]
def findStateAsync {α β σ : Type} [Inhabited σ] (ext : PersistentEnvExtension α β σ)
    (env : Environment) (declPrefix : Name) : σ :=
  ext.toEnvExtension.findStateAsync env declPrefix |>.state


end PersistentEnvExtension

builtin_initialize persistentEnvExtensionsRef : IO.Ref (Array (PersistentEnvExtension EnvExtensionEntry EnvExtensionEntry EnvExtensionState)) ← IO.mkRef #[]

structure PersistentEnvExtensionDescr (α β σ : Type) where
  name            : Name := by exact decl_name%
  mkInitial       : IO σ
  addImportedFn   : Array (Array α) → ImportM σ
  addEntryFn      : σ → β → σ
  exportEntriesFn : σ → Array α
  statsFn         : σ → Format := fun _ => Format.nil
  asyncMode       : EnvExtension.AsyncMode := .mainOnly
  replay?         : Option (ReplayFn σ) := none

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
    exportEntriesFn := descr.exportEntriesFn,
    statsFn         := descr.statsFn
  }
  persistentEnvExtensionsRef.modify fun pExts => pExts.push (unsafeCast pExt)
  return pExt

@[implemented_by registerPersistentEnvExtensionUnsafe]
opaque registerPersistentEnvExtension {α β σ : Type} [Inhabited σ] (descr : PersistentEnvExtensionDescr α β σ) : IO (PersistentEnvExtension α β σ)

/-- Simple `PersistentEnvExtension` that implements `exportEntriesFn` using a list of entries. -/
def SimplePersistentEnvExtension (α σ : Type) := PersistentEnvExtension α α (List α × σ)

@[specialize] def mkStateFromImportedEntries {α σ : Type} (addEntryFn : σ → α → σ) (initState : σ) (as : Array (Array α)) : σ :=
  as.foldl (fun r es => es.foldl (fun r e => addEntryFn r e) r) initState

structure SimplePersistentEnvExtensionDescr (α σ : Type) where
  name          : Name := by exact decl_name%
  addEntryFn    : σ → α → σ
  addImportedFn : Array (Array α) → σ
  toArrayFn     : List α → Array α := fun es => es.toArray
  asyncMode     : EnvExtension.AsyncMode := .mainOnly
  replay?       : Option ((newEntries : List α) → (newState : σ) → σ → List α × σ) := none

/--
Returns a function suitable for `SimplePersistentEnvExtensionDescr.replay?` that replays all new
entries onto the state using `addEntryFn`. `p` should filter out entries that have already been
added to the state by a prior replay of the same realizable constant.
-/
def SimplePersistentEnvExtension.replayOfFilter (p : σ → α → Bool)
    (addEntryFn : σ → α → σ) : List α → σ → σ → List α × σ :=
  fun newEntries _ s =>
    let newEntries := newEntries.filter (p s)
    (newEntries, newEntries.foldl (init := s) addEntryFn)

def registerSimplePersistentEnvExtension {α σ : Type} [Inhabited σ] (descr : SimplePersistentEnvExtensionDescr α σ) : IO (SimplePersistentEnvExtension α σ) :=
  registerPersistentEnvExtension {
    name            := descr.name,
    mkInitial       := pure ([], descr.addImportedFn #[]),
    addImportedFn   := fun as => pure ([], descr.addImportedFn as),
    addEntryFn      := fun s e => match s with
      | (entries, s) => (e::entries, descr.addEntryFn s e),
    exportEntriesFn := fun s => descr.toArrayFn s.1.reverse,
    statsFn := fun s => format "number of local entries: " ++ format s.1.length
    asyncMode := descr.asyncMode
    replay? := descr.replay?.map fun replay oldState newState _ (entries, s) =>
      let newEntries := newState.1.take (newState.1.length - oldState.1.length)
      let (newEntries, s) := replay newEntries newState.2 s
      (entries ++ newEntries, s)
  }

namespace SimplePersistentEnvExtension

instance {α σ : Type} [Inhabited σ] : Inhabited (SimplePersistentEnvExtension α σ) :=
  inferInstanceAs (Inhabited (PersistentEnvExtension α α (List α × σ)))

/-- Get the list of values used to update the state of the given
`SimplePersistentEnvExtension` in the current file. -/
def getEntries {α σ : Type} [Inhabited σ] (ext : SimplePersistentEnvExtension α σ) (env : Environment) : List α :=
  (PersistentEnvExtension.getState ext env).1

/-- Get the current state of the given `SimplePersistentEnvExtension`. -/
def getState {α σ : Type} [Inhabited σ] (ext : SimplePersistentEnvExtension α σ) (env : Environment)
    (asyncMode := ext.toEnvExtension.asyncMode) : σ :=
  (PersistentEnvExtension.getState (asyncMode := asyncMode) ext env).2

/-- Set the current state of the given `SimplePersistentEnvExtension`. This change is *not* persisted across files. -/
def setState {α σ : Type} (ext : SimplePersistentEnvExtension α σ) (env : Environment) (s : σ) : Environment :=
  PersistentEnvExtension.modifyState ext env (fun ⟨entries, _⟩ => (entries, s))

/-- Modify the state of the given extension in the given environment by applying the given function. This change is *not* persisted across files. -/
def modifyState {α σ : Type} (ext : SimplePersistentEnvExtension α σ) (env : Environment) (f : σ → σ) : Environment :=
  PersistentEnvExtension.modifyState ext env (fun ⟨entries, s⟩ => (entries, f s))

@[inherit_doc PersistentEnvExtension.findStateAsync]
def findStateAsync {α σ : Type} [Inhabited σ] (ext : SimplePersistentEnvExtension α σ)
    (env : Environment) (declPrefix : Name) : σ :=
  PersistentEnvExtension.findStateAsync ext env declPrefix |>.2

end SimplePersistentEnvExtension

/-- Environment extension for tagging declarations.
    Declarations must only be tagged in the module where they were declared. -/
def TagDeclarationExtension := SimplePersistentEnvExtension Name NameSet

def mkTagDeclarationExtension (name : Name := by exact decl_name%) : IO TagDeclarationExtension :=
  registerSimplePersistentEnvExtension {
    name          := name,
    addImportedFn := fun _ => {},
    addEntryFn    := fun s n => s.insert n,
    toArrayFn     := fun es => es.toArray.qsort Name.quickLt
    asyncMode     := .async
  }

namespace TagDeclarationExtension

instance : Inhabited TagDeclarationExtension :=
  inferInstanceAs (Inhabited (SimplePersistentEnvExtension Name NameSet))

def tag (ext : TagDeclarationExtension) (env : Environment) (declName : Name) : Environment :=
  have : Inhabited Environment := ⟨env⟩
  assert! env.getModuleIdxFor? declName |>.isNone -- See comment at `TagDeclarationExtension`
  assert! env.asyncMayContain declName
  ext.addEntry env declName

def isTagged (ext : TagDeclarationExtension) (env : Environment) (declName : Name) : Bool :=
  match env.getModuleIdxFor? declName with
  | some modIdx => (ext.getModuleEntries env modIdx).binSearchContains declName Name.quickLt
  | none        => (ext.findStateAsync env declName).contains declName

end TagDeclarationExtension

/-- Environment extension for mapping declarations to values.
    Declarations must only be inserted into the mapping in the module where they were declared. -/

structure MapDeclarationExtension (α : Type) extends PersistentEnvExtension (Name × α) (Name × α) (NameMap α)
deriving Inhabited

def mkMapDeclarationExtension (name : Name := by exact decl_name%) : IO (MapDeclarationExtension α) :=
  .mk <$> registerPersistentEnvExtension {
    name            := name,
    mkInitial       := pure {}
    addImportedFn   := fun _ => pure {}
    addEntryFn      := fun s (n, v) => s.insert n v
    exportEntriesFn := fun s => s.toArray
    asyncMode       := .async
    replay?         := some fun _ newState newConsts s =>
      newConsts.foldl (init := s) fun s c =>
        if let some a := newState.find? c then
          s.insert c a
        else s
  }

namespace MapDeclarationExtension

def insert (ext : MapDeclarationExtension α) (env : Environment) (declName : Name) (val : α) : Environment :=
  have : Inhabited Environment := ⟨env⟩
  assert! env.getModuleIdxFor? declName |>.isNone -- See comment at `MapDeclarationExtension`
  assert! env.asyncMayContain declName
  ext.addEntry env (declName, val)

def find? [Inhabited α] (ext : MapDeclarationExtension α) (env : Environment) (declName : Name) : Option α :=
  match env.getModuleIdxFor? declName with
  | some modIdx =>
    match (ext.getModuleEntries env modIdx).binSearch (declName, default) (fun a b => Name.quickLt a.1 b.1) with
    | some e => some e.2
    | none   => none
  | none => (ext.findStateAsync env declName).find? declName

def contains [Inhabited α] (ext : MapDeclarationExtension α) (env : Environment) (declName : Name) : Bool :=
  match env.getModuleIdxFor? declName with
  | some modIdx => (ext.getModuleEntries env modIdx).binSearchContains (declName, default) (fun a b => Name.quickLt a.1 b.1)
  | none        => (ext.findStateAsync env declName).contains declName

end MapDeclarationExtension

@[extern "lean_save_module_data"]
opaque saveModuleData (fname : @& System.FilePath) (mod : @& Name) (data : @& ModuleData) : IO Unit
@[extern "lean_read_module_data"]
opaque readModuleData (fname : @& System.FilePath) : IO (ModuleData × CompactedRegion)

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

def mkModuleData (env : Environment) : IO ModuleData := do
  let pExts ← persistentEnvExtensionsRef.get
  let entries := pExts.map fun pExt => Id.run do
    -- get state from `checked` at the end if `async`; it would otherwise panic
    let mut asyncMode := pExt.toEnvExtension.asyncMode
    if asyncMode matches .async then
      asyncMode := .sync
    let state := pExt.getState (asyncMode := asyncMode) env
    (pExt.name, pExt.exportEntriesFn state)
  let kenv := env.toKernelEnv
  let constNames := kenv.constants.foldStage2 (fun names name _ => names.push name) #[]
  let constants  := kenv.constants.foldStage2 (fun cs _ c => cs.push c) #[]
  return {
    imports         := env.header.imports
    extraConstNames := env.checked.get.extraConstNames.toArray
    constNames, constants, entries
  }

@[export lean_write_module]
def writeModule (env : Environment) (fname : System.FilePath) : IO Unit := do
  saveModuleData fname env.mainModule (← mkModuleData env)

/--
Construct a mapping from persistent extension name to extension index at the array of persistent extensions.
We only consider extensions starting with index `>= startingAt`.
-/
def mkExtNameMap (startingAt : Nat) : IO (Std.HashMap Name Nat) := do
  let descrs ← persistentEnvExtensionsRef.get
  let mut result := {}
  for h : i in [startingAt : descrs.size] do
    let descr := descrs[i]
    result := result.insert descr.name i
  return result

private def setImportedEntries (env : Environment) (mods : Array ModuleData) (startingAt : Nat := 0) : IO Environment := do
  -- We work directly on the states array instead of `env` as `Environment.modifyState` introduces
  -- significant overhead on such frequent calls
  let mut states := env.base.extensions
  let extDescrs ← persistentEnvExtensionsRef.get
  /- For extensions starting at `startingAt`, ensure their `importedEntries` array have size `mods.size`. -/
  for extDescr in extDescrs[startingAt:] do
    -- safety: as in `modifyState`
    states := unsafe extDescr.toEnvExtension.modifyStateImpl states fun s =>
      { s with importedEntries := mkArray mods.size #[] }
  /- For each module `mod`, and `mod.entries`, if the extension name is one of the extensions after `startingAt`, set `entries` -/
  let extNameIdx ← mkExtNameMap startingAt
  for h : modIdx in [:mods.size] do
    let mod := mods[modIdx]
    for (extName, entries) in mod.entries do
      if let some entryIdx := extNameIdx[extName]? then
        -- safety: as in `modifyState`
        states := unsafe extDescrs[entryIdx]!.toEnvExtension.modifyStateImpl states fun s =>
          { s with importedEntries := s.importedEntries.set! modIdx entries }
  return env.setCheckedSync { env.base with extensions := states }

/--
  "Forward declaration" needed for updating the attribute table with user-defined attributes.
  User-defined attributes are declared using the `initialize` command. The `initialize` command is just syntax sugar for the `init` attribute.
  The `init` attribute is initialized after the `attributeExtension` is initialized. We cannot change the order since the `init` attribute is an attribute,
  and requires this extension.
  The `attributeExtension` initializer uses `attributeMapRef` to initialize the attribute mapping.
  When we a new user-defined attribute declaration is imported, `attributeMapRef` is updated.
  Later, we set this method with code that adds the user-defined attributes that were imported after we initialized `attributeExtension`.
-/
@[extern 2 "lean_update_env_attributes"] opaque updateEnvAttributes : Environment → IO Environment
/-- "Forward declaration" for retrieving the number of builtin attributes. -/
@[extern 1 "lean_get_num_attributes"] opaque getNumBuiltinAttributes : IO Nat

private def ensureExtensionsArraySize (env : Environment) : IO Environment := do
  let exts ← EnvExtension.ensureExtensionsArraySize env.base.extensions
  return env.modifyCheckedAsync ({ · with extensions := exts })

private partial def finalizePersistentExtensions (env : Environment) (mods : Array ModuleData) (opts : Options) : IO Environment := do
  loop 0 env
where
  loop (i : Nat) (env : Environment) : IO Environment := do
    -- Recall that the size of the array stored `persistentEnvExtensionRef` may increase when we import user-defined environment extensions.
    let pExtDescrs ← persistentEnvExtensionsRef.get
    if h : i < pExtDescrs.size then
      let extDescr := pExtDescrs[i]
      -- `local` as `async` does not allow for `getState` but it's all safe here as there is only
      -- one branch so far.
      let s := extDescr.toEnvExtension.getState (asyncMode := .local) env
      let prevSize := (← persistentEnvExtensionsRef.get).size
      let prevAttrSize ← getNumBuiltinAttributes
      let newState ← extDescr.addImportedFn s.importedEntries { env := env, opts := opts }
      let mut env := extDescr.toEnvExtension.setState env { s with state := newState }
      env ← ensureExtensionsArraySize env
      if (← persistentEnvExtensionsRef.get).size > prevSize || (← getNumBuiltinAttributes) > prevAttrSize then
        -- This branch is executed when `pExtDescrs[i]` is the extension associated with the `init` attribute, and
        -- a user-defined persistent extension is imported.
        -- Thus, we invoke `setImportedEntries` to update the array `importedEntries` with the entries for the new extensions.
        env ← setImportedEntries env mods prevSize
        -- See comment at `updateEnvAttributesRef`
        env ← updateEnvAttributes env
      loop (i + 1) env
    else
      return env

structure ImportState where
  moduleNameSet : NameHashSet := {}
  moduleNames   : Array Name := #[]
  moduleData    : Array ModuleData := #[]
  regions       : Array CompactedRegion := #[]

def throwAlreadyImported (s : ImportState) (const2ModIdx : Std.HashMap Name ModuleIdx) (modIdx : Nat) (cname : Name) : IO α := do
  let modName := s.moduleNames[modIdx]!
  let constModName := s.moduleNames[const2ModIdx[cname]!.toNat]!
  throw <| IO.userError s!"import {modName} failed, environment already contains '{cname}' from {constModName}"

abbrev ImportStateM := StateRefT ImportState IO

@[inline] nonrec def ImportStateM.run (x : ImportStateM α) (s : ImportState := {}) : IO (α × ImportState) :=
  x.run s

partial def importModulesCore (imports : Array Import) : ImportStateM Unit := do
  for i in imports do
    if i.runtimeOnly || (← get).moduleNameSet.contains i.module then
      continue
    modify fun s => { s with moduleNameSet := s.moduleNameSet.insert i.module }
    let mFile ← findOLean i.module
    unless (← mFile.pathExists) do
      throw <| IO.userError s!"object file '{mFile}' of module {i.module} does not exist"
    let (mod, region) ← readModuleData mFile
    importModulesCore mod.imports
    modify fun s => { s with
      moduleData  := s.moduleData.push mod
      regions     := s.regions.push region
      moduleNames := s.moduleNames.push i.module
    }

/--
Return `true` if `cinfo₁` and `cinfo₂` are theorems with the same name, universe parameters,
and types. We allow different modules to prove the same theorem.

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
private def equivInfo (cinfo₁ cinfo₂ : ConstantInfo) : Bool := Id.run do
  let .thmInfo tval₁ := cinfo₁ | false
  let .thmInfo tval₂ := cinfo₂ | false
  return tval₁.name == tval₂.name
    && tval₁.type == tval₂.type
    && tval₁.levelParams == tval₂.levelParams
    && tval₁.all == tval₂.all

/--
  Construct environment from `importModulesCore` results.

  If `leakEnv` is true, we mark the environment as persistent, which means it
  will not be freed. We set this when the object would survive until the end of
  the process anyway. In exchange, RC updates are avoided, which is especially
  important when they would be atomic because the environment is shared across
  threads (potentially, storing it in an `IO.Ref` is sufficient for marking it
  as such). -/
def finalizeImport (s : ImportState) (imports : Array Import) (opts : Options) (trustLevel : UInt32 := 0)
    (leakEnv := false) : IO Environment := do
  let numConsts := s.moduleData.foldl (init := 0) fun numConsts mod =>
    numConsts + mod.constants.size + mod.extraConstNames.size
  let mut const2ModIdx : Std.HashMap Name ModuleIdx := Std.HashMap.empty (capacity := numConsts)
  let mut constantMap : Std.HashMap Name ConstantInfo := Std.HashMap.empty (capacity := numConsts)
  for h : modIdx in [0:s.moduleData.size] do
    let mod := s.moduleData[modIdx]
    for cname in mod.constNames, cinfo in mod.constants do
      match constantMap.getThenInsertIfNew? cname cinfo with
      | (cinfoPrev?, constantMap') =>
        constantMap := constantMap'
        if let some cinfoPrev := cinfoPrev? then
          -- Recall that the map has not been modified when `cinfoPrev? = some _`.
          unless equivInfo cinfoPrev cinfo do
            throwAlreadyImported s const2ModIdx modIdx cname
      const2ModIdx := const2ModIdx.insertIfNew cname modIdx
    for cname in mod.extraConstNames do
      const2ModIdx := const2ModIdx.insertIfNew cname modIdx
  let constants : ConstMap := SMap.fromHashMap constantMap false
  let exts ← mkInitialExtensionStates
  let mut env : Environment := {
    base := {
      const2ModIdx, constants
      quotInit        := !imports.isEmpty -- We assume `core.lean` initializes quotient module
      extraConstNames := {}
      extensions      := exts
      header     := {
        trustLevel, imports
        regions      := s.regions
        moduleNames  := s.moduleNames
        moduleData   := s.moduleData
      }
    }
    realizedImportedConsts? := none
  }
  env ← setImportedEntries env s.moduleData
  if leakEnv then
    /- Mark persistent a first time before `finalizePersistenExtensions`, which
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
  env ← finalizePersistentExtensions env s.moduleData opts
  if leakEnv then
    /- Ensure the final environment including environment extension states is
       marked persistent as documented.

       Safety: There are no concurrent accesses to `env` at this point, assuming
       extensions' `addImportFn`s did not spawn any unbound tasks. -/
    env ← unsafe Runtime.markPersistent env
  pure env

@[export lean_import_modules]
def importModules (imports : Array Import) (opts : Options) (trustLevel : UInt32 := 0)
    (plugins : Array System.FilePath := #[]) (leakEnv := false)
    : IO Environment := profileitIO "import" opts do
  for imp in imports do
    if imp.module matches .anonymous then
      throw <| IO.userError "import failed, trying to import module with anonymous name"
  withImporting do
    plugins.forM Lean.loadPlugin
    let (_, s) ← importModulesCore imports |>.run
    finalizeImport (leakEnv := leakEnv) s imports opts trustLevel

/--
  Create environment object from imports and free compacted regions after calling `act`. No live references to the
  environment object or imported objects may exist after `act` finishes. -/
unsafe def withImportModules {α : Type} (imports : Array Import) (opts : Options) (trustLevel : UInt32 := 0) (act : Environment → IO α) : IO α := do
  let env ← importModules imports opts trustLevel
  try act env finally env.freeRegions

@[inherit_doc Kernel.Environment.enableDiag]
def Kernel.enableDiag (env : Lean.Environment) (flag : Bool) : Lean.Environment :=
  env.modifyCheckedAsync (·.enableDiag flag)

def Kernel.isDiagnosticsEnabled (env : Lean.Environment) : Bool :=
  env.base.isDiagnosticsEnabled

def Kernel.resetDiag (env : Lean.Environment) : Lean.Environment :=
  env.modifyCheckedAsync (·.resetDiag)

def Kernel.getDiagnostics (env : Lean.Environment) : Diagnostics :=
  env.checked.get.diagnostics

def Kernel.setDiagnostics (env : Lean.Environment) (diag : Diagnostics) : Lean.Environment :=
  env.modifyCheckedAsync (·.setDiagnostics diag)

namespace Environment

@[export lean_elab_environment_update_base_after_kernel_add]
private def updateBaseAfterKernelAdd (env : Environment) (kenv : Kernel.Environment) (decl : Declaration) : Environment :=
  { env with
    checked := .pure kenv
    -- make constants available in `asyncConsts` as well; see its docstring
    asyncConsts := decl.getNames.foldl (init := env.asyncConsts) fun asyncConsts n =>
      if asyncConsts.find? n |>.isNone then
        asyncConsts.add {
          constInfo := .ofConstantInfo (kenv.find? n |>.get!)
          exts? := none
          consts := .pure <| .mk (α := AsyncConsts) default
        }
      else asyncConsts }

@[export lean_display_stats]
def displayStats (env : Environment) : IO Unit := do
  let pExtDescrs ← persistentEnvExtensionsRef.get
  IO.println ("direct imports:                        " ++ toString env.header.imports);
  IO.println ("number of imported modules:            " ++ toString env.header.regions.size);
  IO.println ("number of memory-mapped modules:       " ++ toString (env.header.regions.filter (·.isMemoryMapped) |>.size));
  IO.println ("number of buckets for imported consts: " ++ toString env.constants.numBuckets);
  IO.println ("trust level:                           " ++ toString env.header.trustLevel);
  IO.println ("number of extensions:                  " ++ toString env.base.extensions.size);
  pExtDescrs.forM fun extDescr => do
    IO.println ("extension '" ++ toString extDescr.name ++ "'")
    -- get state from `checked` at the end if `async`; it would otherwise panic
    let mut asyncMode := extDescr.toEnvExtension.asyncMode
    if asyncMode matches .async then
      asyncMode := .sync
    let s := extDescr.toEnvExtension.getState (asyncMode := asyncMode) env
    let fmt := extDescr.statsFn s.state
    unless fmt.isNil do IO.println ("  " ++ toString (Format.nest 2 (extDescr.statsFn s.state)))
    IO.println ("  number of imported entries: " ++ toString (s.importedEntries.foldl (fun sum es => sum + es.size) 0))

/--
  Evaluate the given declaration under the given environment to a value of the given type.
  This function is only safe to use if the type matches the declaration's type in the environment
  and if `enableInitializersExecution` has been used before importing any modules. -/
@[extern "lean_eval_const"]
unsafe opaque evalConst (α) (env : @& Environment) (opts : @& Options) (constName : @& Name) : Except String α

private def throwUnexpectedType {α} (typeName : Name) (constName : Name) : ExceptT String Id α :=
  throw ("unexpected type at '" ++ toString constName ++ "', `" ++ toString typeName ++ "` expected")

/-- Like `evalConst`, but first check that `constName` indeed is a declaration of type `typeName`.
    Note that this function cannot guarantee that `typeName` is in fact the name of the type `α`. -/
unsafe def evalConstCheck (α) (env : Environment) (opts : Options) (typeName : Name) (constName : Name) : ExceptT String Id α :=
  match env.find? constName with
  | none      => throw ("unknown constant '" ++ toString constName ++ "'")
  | some info =>
    match info.type with
    | Expr.const c _ =>
      if c != typeName then throwUnexpectedType typeName constName
      else env.evalConst α opts constName
    | _ => throwUnexpectedType typeName constName

def hasUnsafe (env : Environment) (e : Expr) : Bool :=
  let c? := e.find? fun e => match e with
    | Expr.const c _ =>
      match env.find? c with
      | some cinfo => cinfo.isUnsafe
      | none       => false
    | _ => false;
  c?.isSome

/-- Plumbing function for `Lean.Meta.realizeConst`; see documentation there. -/
def realizeConst (env : Environment) (forConst : Name) (constName : Name)
    (realize : Environment → Options → BaseIO (Environment × Dynamic)) :
    IO (Environment × Dynamic) := do
  let mut env := env
  -- find `RealizationContext` for `forConst` in `realizedImportedConsts?` or `realizedLocalConsts`
  let ctx ← if env.base.const2ModIdx.contains forConst then
    env.realizedImportedConsts?.getDM <|
      throw <| .userError s!"Environment.realizeConst: `realizedImportedConsts` is empty"
  else
    match env.realizedLocalConsts.find? forConst with
    | some ctx => pure ctx
    | none =>
      throw <| .userError s!"trying to realize {constName} but `enableRealizationsForConst` must be called for '{forConst}' first"
  let prom ← IO.Promise.new
  -- ensure `prom` is not left unresolved from stray exceptions
  BaseIO.toIO do
    -- atomically check whether we are the first branch to realize `constName`
    let existingConsts? ← ctx.constsRef.modifyGet fun m => match m.find? constName with
      | some prom' => (some prom', m)
      | none       => (none, m.insert constName prom.result!)
    let (consts, replay, dyn) ← if let some existingConsts := existingConsts? then
      pure existingConsts.get
    else
      -- safety: `RealizationContext` is private
      let realizeEnv : Environment := unsafe unsafeCast ctx.env
      let realizeEnv := { realizeEnv with
        -- allow realizations to recursively realize other constants for `forConst`. Do note that
        -- this allows for recursive realization of `constName` itself, which will deadlock.
        realizedLocalConsts := realizeEnv.realizedLocalConsts.insert forConst ctx
        realizedImportedConsts? := env.realizedImportedConsts?
      }
      -- ensure realized constants are nested below `forConst` and that environment extension
      -- modifications know they are in an async context
      let realizeEnv := realizeEnv.enterAsync (realizing := true) forConst
      -- skip kernel in `realize`, we'll re-typecheck anyway
      let realizeOpts := debug.skipKernelTC.set ctx.opts true
      let (realizeEnv', dyn) ← realize realizeEnv realizeOpts
      -- We could check that `c` was indeed added here but in practice `realize` has already
      -- reported an error so we don't.

      -- find new constants incl. nested realizations, add current extension state, and compute
      -- closure
      let numNewConsts := realizeEnv'.asyncConsts.size - realizeEnv.asyncConsts.size
      let consts := realizeEnv'.asyncConsts.revList.take numNewConsts |>.reverse
      let consts := consts.map fun c =>
        if c.exts?.isNone then
          { c with exts? := some <| .pure realizeEnv'.base.extensions }
        else c
      let exts ← EnvExtension.envExtensionsRef.get
      let replay := (maybeAddToKernelEnv realizeEnv realizeEnv' consts · exts)
      prom.resolve (consts, replay, dyn)
      pure (consts, replay, dyn)
    return ({ env with
      asyncConsts := consts.foldl (init := env.asyncConsts) fun consts c =>
        if consts.find? c.constInfo.name |>.isSome then
          consts
        else
          consts.add c
      checked := env.checked.map replay
    }, dyn)
where
  -- Adds `consts` if they haven't already been added by a previous branch. Note that this
  -- conditional is deterministic because of the linearizing effect of `env.checked`.
  maybeAddToKernelEnv (oldEnv newEnv : Environment) (consts : List AsyncConst)
      (kenv : Kernel.Environment)
      (exts : Array (EnvExtension EnvExtensionState)) : Kernel.Environment := Id.run do
    let mut kenv := kenv
    for c in consts do
      if kenv.find? c.constInfo.name |>.isSome then
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
        | .thmInfo thm   => .thmDecl thm
        | .defnInfo defn => .defnDecl defn
        | _              =>
          return panic! s!"{c.constInfo.name} must be definition/theorem"
      -- realized kernel additions cannot be interrupted - which would be bad anyway as they can be
      -- reused between snapshots
      match kenv.addDeclCore 0 decl none with
      | .ok kenv' => kenv := kenv'
      | .error e =>
        return panic! s!"failed to add {c.constInfo.name} to environment\n{e.toRawString}"
    for ext in exts do
      if let some replay := ext.replay? then
        kenv := { kenv with
          -- safety: like in `modifyState`, but that one takes an elab env instead of a kernel env
          extensions := unsafe (ext.modifyStateImpl kenv.extensions <|
            replay
              (ext.getStateImpl oldEnv.toKernelEnv.extensions)
              (ext.getStateImpl newEnv.toKernelEnv.extensions)
              (consts.map (·.constInfo.name))) }
    return kenv

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

@[always_inline]
instance (m n) [MonadLift m n] [MonadEnv m] : MonadEnv n where
  getEnv    := liftM (getEnv : m Environment)
  modifyEnv := fun f => liftM (modifyEnv f : m Unit)

/-- Constructs a DefinitionVal, inferring the `unsafe` field -/
def mkDefinitionValInferrringUnsafe [Monad m] [MonadEnv m] (name : Name) (levelParams : List Name)
    (type : Expr) (value : Expr) (hints : ReducibilityHints) : m DefinitionVal := do
  let env ← getEnv
  let safety := if env.hasUnsafe type || env.hasUnsafe value then DefinitionSafety.unsafe else DefinitionSafety.safe
  return { name, levelParams, type, value, hints, safety }

def getMaxHeight (env : Environment) (e : Expr) : UInt32 :=
  e.foldConsts 0 fun constName max =>
    match env.find? constName with
    | ConstantInfo.defnInfo val =>
      match val.hints with
      | ReducibilityHints.regular h => if h > max then h else max
      | _                           => max
    | _ => max

end Lean
