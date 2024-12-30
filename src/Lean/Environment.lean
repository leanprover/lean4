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
import Lean.PrivateName

namespace Lean
/-- Opaque environment extension state. -/
opaque EnvExtensionStateSpec : (α : Type) × Inhabited α := ⟨Unit, ⟨()⟩⟩
def EnvExtensionState : Type := EnvExtensionStateSpec.fst
instance : Inhabited EnvExtensionState := EnvExtensionStateSpec.snd

def ModuleIdx := Nat
  deriving BEq, ToString

abbrev ModuleIdx.toNat (midx : ModuleIdx) : Nat := midx

instance : Inhabited ModuleIdx where default := (0 : Nat)

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
  /-- Name of all imported modules (directly and indirectly). -/
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
  | «axiom» | defn | thm | «opaque» | quot | induct | ctor | recursor
deriving Inhabited, BEq, Repr

def ConstantKind.ofConstantInfo : ConstantInfo → ConstantKind
  | .defnInfo   _ => .defn
  | .axiomInfo  _ => .axiom
  | .thmInfo    _ => .thm
  | .opaqueInfo _ => .opaque
  | .quotInfo   _ => .quot
  | .inductInfo _ => .induct
  | .ctorInfo   _ => .ctor
  | .recInfo    _ => .recursor

/-- `ConstantInfo` variant that allows for asynchronous filling of components via tasks. -/
structure AsyncConstantInfo where
  /-- The declaration name, known immediately. -/
  name : Name
  /-- The kind of the constant, known immediately. -/
  kind : ConstantKind
  /-- The "signature" including level params and type, potentially filled asynchronously. -/
  sig  : Task ConstantVal
  /-- The final, complete constant info, potentially filled asynchronously. -/
  info : Task ConstantInfo

namespace AsyncConstantInfo

def toConstantVal (c : AsyncConstantInfo) : ConstantVal :=
  c.sig.get

def toConstantInfo (c : AsyncConstantInfo) : ConstantInfo :=
  c.info.get

def ofConstantInfo (c : ConstantInfo) : AsyncConstantInfo where
  name := c.name
  kind := .ofConstantInfo c
  sig := .pure c.toConstantVal
  info := .pure c

end AsyncConstantInfo

/--
Information about the current branch of the environment representing asynchronous elaboration.
-/
structure AsyncContext where
  /--
  Name of the declaration asynchronous elaboration was started for. All constants added to this
  environment branch must have the name as a prefix, after erasing macro scopes and private name
  prefixes.
  -/
  declPrefix : Name
deriving Nonempty

/--
Checks whether a declaration named `n` may be added to the environment in the given context. See
also `AsyncContext.declPrefix`.
-/
def AsyncContext.mayContain (ctx : AsyncContext) (n : Name) : Bool :=
  ctx.declPrefix.isPrefixOf <| privateToUserName n.eraseMacroScopes

/--
Constant info and environment extension states eventually resulting from async elaboration.
-/
structure AsyncConst where
  info : AsyncConstantInfo
  exts? : Option (Task (Array EnvExtensionState))

/-- Data structure holding a sequence of `AsyncConst`s optimized for efficient access. -/
structure AsyncConsts where
  toArray : Array AsyncConst := #[]
  /-- Map from declaration name to const for fast direct access. -/
  private map : NameMap AsyncConst := {}
  /-- Trie of declaration names without private name prefixes for fast longest-prefix access. -/
  private normalizedTrie : NameTrie AsyncConst := {}
deriving Inhabited

def AsyncConsts.add (aconsts : AsyncConsts) (aconst : AsyncConst) : AsyncConsts :=
  { aconsts with
    toArray := aconsts.toArray.push aconst
    map := aconsts.map.insert aconst.info.name aconst
    normalizedTrie := aconsts.normalizedTrie.insert (privateToUserName aconst.info.name) aconst
  }

def AsyncConsts.find? (aconsts : AsyncConsts) (declName : Name) : Option AsyncConst :=
  aconsts.map.find? declName

/-- Checks whether the name of any constant in the collection is a prefix of `declName`. -/
def AsyncConsts.hasPrefix (aconsts : AsyncConsts) (declName : Name) : Bool :=
  -- as macro scopes are a strict suffix,
  aconsts.normalizedTrie.findLongestPrefix? (privateToUserName declName.eraseMacroScopes) |>.isSome

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
  checkedWithoutAsync : Kernel.Environment
  checked             : Task Kernel.Environment := .pure checkedWithoutAsync
  asyncConsts         : AsyncConsts := {}
  private asyncCtx?       : Option AsyncContext := none
deriving Nonempty

namespace Environment

@[export lean_elab_environment_of_kernel_env]
def ofKernelEnv (env : Kernel.Environment) : Environment :=
  { checkedWithoutAsync := env }

@[export lean_elab_environment_to_kernel_env]
def toKernelEnv (env : Environment) : Kernel.Environment :=
  env.checked.get

private def modifyCheckedAsync (env : Environment) (f : Kernel.Environment → Kernel.Environment) : Environment :=
  { env with checked := env.checked.map (sync := true) f, checkedWithoutAsync := f env.checkedWithoutAsync }

private def setCheckedSync (env : Environment) (newChecked : Kernel.Environment) : Environment :=
  { env with checked := .pure newChecked, checkedWithoutAsync := newChecked }

/-- Type check given declaration and add it to the environment. -/
@[extern "lean_elab_add_decl"]
opaque addDeclCore (env : Environment) (maxHeartbeats : USize) (decl : @& Declaration)
  (cancelTk? : @& Option IO.CancelToken) : Except Kernel.Exception Environment

@[inherit_doc Kernel.Environment.addDeclWithoutChecking, extern "lean_elab_add_decl_without_checking"]
opaque addDeclWithoutChecking (env : Environment) (decl : @& Declaration) : Except Kernel.Exception Environment

@[inherit_doc Kernel.Environment.constants]
def constants (env : Environment) : ConstMap :=
  env.toKernelEnv.constants

@[inherit_doc Kernel.Environment.const2ModIdx]
def const2ModIdx (env : Environment) : Std.HashMap Name ModuleIdx :=
  env.toKernelEnv.const2ModIdx

@[export lean_elab_environment_add]
private def add (env : Environment) (cinfo : ConstantInfo) : Environment :=
  { env with checkedWithoutAsync := env.checkedWithoutAsync.add cinfo }

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

private def findNoAsyncTheorem (env : Environment) (n : Name) : Option ConstantInfo := do
  if env.asyncConsts.hasPrefix n then
    -- Constant generated in a different elaboration thread: wait for final kernel environment. Rare
    -- case when only proofs are elaborated asynchronously as they are rarely inspected. Could be
    -- optimized in the future by having the elaboration thread publish an (incremental?) map of
    -- generated declarations before kernel checking (which must wait on all previous threads).
    env.checked.get.constants.find?' n
  else
    -- Not in the kernel environment nor in the name prefix of any elaboration thread: undefined by
    -- `addDecl` invariant. Except for realizable constants :( .
    none

def findAsync? (env : Environment) (n : Name) : Option AsyncConstantInfo := do
  -- Check declarations already added to the kernel environment (e.g. because they were imported)
  -- first as that should be the most common case. It is safe to use `find?'` because we never
  -- overwrite imported declarations.
  if let some c := env.checkedWithoutAsync.constants.find?' n then
    some <| .ofConstantInfo c
  else if let some asyncConst := env.asyncConsts.find? n then
    -- Constant for which an asynchronous elaboration task was spawned
    return asyncConst.info
  else env.findNoAsyncTheorem n |>.map .ofConstantInfo

def dbgFormatAsyncState (env : Environment) : BaseIO String :=
  return s!"\
    asyncCtx.declPrefix: {repr <| env.asyncCtx?.map (·.declPrefix)}\
  \nasyncConsts: {repr <| env.asyncConsts.toArray.map (·.info.name)}\
  \ncheckedWithoutAsync.constants.map₂: {repr <| env.checkedWithoutAsync.constants.map₂.toList.map (·.1)}"

def dbgFormatCheckedSyncState (env : Environment) : BaseIO String :=
  return s!"checked.get.constants.map₂: {repr <| env.checked.get.constants.map₂.toList.map (·.1)}"

def findConstVal? (env : Environment) (n : Name) : Option ConstantVal := do
  if let some c := env.checkedWithoutAsync.constants.find?' n then
    some c.toConstantVal
  else if let some asyncConst := env.asyncConsts.find? n then
    return asyncConst.info.toConstantVal
  else env.findNoAsyncTheorem n |>.map (·.toConstantVal)

def find? (env : Environment) (n : Name) : Option ConstantInfo :=
  if let some c := env.checkedWithoutAsync.constants.find?' n then
    some c
  else if let some asyncConst := env.asyncConsts.find? n then
    return asyncConst.info.toConstantInfo
  else
    env.findNoAsyncTheorem n

structure AddConstAsyncResult where
  private constName : Name
  private kind : ConstantKind
  mainEnv : Environment
  asyncEnv : Environment
  private sigPromise : IO.Promise ConstantVal
  private infoPromise : IO.Promise ConstantInfo
  private extensionsPromise : IO.Promise (Array EnvExtensionState)
  private checkedEnvPromise : IO.Promise Kernel.Environment

def addConstAsync (env : Environment) (constName : Name) (kind : ConstantKind) (reportExts := true) :
    IO AddConstAsyncResult := do
  let sigPromise ← IO.Promise.new
  let infoPromise ← IO.Promise.new
  let extensionsPromise ← IO.Promise.new
  let checkedEnvPromise ← IO.Promise.new
  let asyncConst := {
    info := {
      name := constName
      kind
      sig := sigPromise.result
      info := infoPromise.result
    }
    exts? := guard reportExts *> some extensionsPromise.result
  }
  return {
    constName, kind
    mainEnv := { env with
      asyncConsts := env.asyncConsts.add asyncConst
      checked := checkedEnvPromise.result }
    asyncEnv := { env with
      asyncCtx? := some { declPrefix := privateToUserName constName }
    }
    sigPromise, infoPromise, extensionsPromise, checkedEnvPromise
  }

def AddConstAsyncResult.commitSignature (res : AddConstAsyncResult) (sig : ConstantVal) :
    IO Unit := do
  if sig.name != res.constName then
    throw <| .userError s!"AddConstAsyncResult.commitSignature: constant has name {sig.name} but expected {res.constName}"
  res.sigPromise.resolve sig

def AddConstAsyncResult.commitConst (res : AddConstAsyncResult) (env : Environment) (info? : Option ConstantInfo := none) :
    IO Unit := do
  let some _ := env.asyncCtx?
    | throw <| .userError "AddConstAsyncResult.commitConst: environment does not have an async context"
  let info ← match info? <|> env.find? res.constName with
    | some info => pure info
    | none =>
      throw <| .userError s!"AddConstAsyncResult.commitConst: constant {res.constName} not found in async context"
  res.commitSignature info.toConstantVal
  let kind' := .ofConstantInfo info
  if res.kind != kind' then
    throw <| .userError s!"AddConstAsyncResult.commitConst: constant has kind {repr kind'} but expected {repr res.kind}"
  let sig := res.sigPromise.result.get
  if sig.levelParams != info.levelParams then
    throw <| .userError s!"AddConstAsyncResult.commitConst: constant has level params {info.levelParams} but expected {sig.levelParams}"
  if sig.type != info.type then
    throw <| .userError s!"AddConstAsyncResult.commitConst: constant has type {info.type} but expected {sig.type}"
  res.infoPromise.resolve info
  res.extensionsPromise.resolve env.checkedWithoutAsync.extensions

def AddConstAsyncResult.commitFailure (res : AddConstAsyncResult) : BaseIO Unit := do
  res.sigPromise.resolve { name := res.constName, levelParams := [], type := mkApp2 (mkConst ``sorryAx [0]) (mkSort 0) (mkConst ``true) }
  res.infoPromise.resolve /- TODO -/ default
  res.extensionsPromise.resolve #[]
  let _ ← BaseIO.mapTask (t := res.asyncEnv.checked) (sync := true) res.checkedEnvPromise.resolve

def AddConstAsyncResult.checkAndCommitEnv (res : AddConstAsyncResult) (env : Environment) :
    IO Unit := do
  let some _ := env.asyncCtx?
    | throw <| .userError "AddConstAsyncResult.checkAndCommitEnv: environment does not have an async context"
  let some _ := env.findAsync? res.constName
    | throw <| .userError s!"AddConstAsyncResult.checkAndCommitEnv: constant {res.constName} not found in async context"
  res.commitConst env
  res.checkedEnvPromise.resolve env.checked.get

def contains (env : Environment) (n : Name) : Bool :=
  env.findAsync? n |>.isSome

def header (env : Environment) : EnvironmentHeader :=
  -- can be assumed to be in sync with `env.checked`; see `setMainModule`, the only modifier of the header
  env.checkedWithoutAsync.header

def imports (env : Environment) : Array Import :=
  env.header.imports

def allImportedModuleNames (env : Environment) : Array Name :=
  env.header.moduleNames

def setMainModule (env : Environment) (m : Name) : Environment :=
  env.modifyCheckedAsync ({ · with header.mainModule := m })

def mainModule (env : Environment) : Name :=
  env.header.mainModule

def getModuleIdxFor? (env : Environment) (declName : Name) : Option ModuleIdx :=
  -- async constants are always from the current module
  env.checkedWithoutAsync.const2ModIdx[declName]?

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

/-- Interface for managing environment extensions. -/
structure EnvExtensionInterface where
  ext          : Type → Type
  inhabitedExt : Inhabited σ → Inhabited (ext σ)
  registerExt  (mkInitial : IO σ) : IO (ext σ)
  setState     (e : ext σ) (exts : Array EnvExtensionState) : σ → Array EnvExtensionState
  modifyState  (e : ext σ) (exts : Array EnvExtensionState) : (σ → σ) → Array EnvExtensionState
  getState     [Inhabited σ] (e : ext σ) (exts : Array EnvExtensionState) : σ
  mkInitialExtStates : IO (Array EnvExtensionState)
  ensureExtensionsSize : Array EnvExtensionState → IO (Array EnvExtensionState)

instance : Inhabited EnvExtensionInterface where
  default := {
    ext                  := id
    inhabitedExt         := id
    ensureExtensionsSize := fun exts => pure exts
    registerExt          := fun mk => mk
    setState             := fun _ exts _ => exts
    modifyState          := fun _ exts _ => exts
    getState             := fun ext _ => ext
    mkInitialExtStates   := pure #[]
  }

/-! # Unsafe implementation of `EnvExtensionInterface` -/
namespace EnvExtensionInterfaceUnsafe

structure Ext (σ : Type) where
  idx       : Nat
  mkInitial : IO σ
  deriving Inhabited

private builtin_initialize envExtensionsRef : IO.Ref (Array (Ext EnvExtensionState)) ← IO.mkRef #[]

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

unsafe def setState {σ} (ext : Ext σ) (exts : Array EnvExtensionState) (s : σ) : Array EnvExtensionState :=
  if h : ext.idx < exts.size then
    exts.set ext.idx (unsafeCast s)
  else
    have : Inhabited (Array EnvExtensionState) := ⟨exts⟩
    panic! invalidExtMsg

@[inline] unsafe def modifyState {σ : Type} (ext : Ext σ) (exts : Array EnvExtensionState) (f : σ → σ) : Array EnvExtensionState :=
  if ext.idx < exts.size then
    exts.modify ext.idx fun s =>
      let s : σ := unsafeCast s
      let s : σ := f s
      unsafeCast s
  else
    have : Inhabited (Array EnvExtensionState) := ⟨exts⟩
    panic! invalidExtMsg

unsafe def getState {σ} [Inhabited σ] (ext : Ext σ) (exts : Array EnvExtensionState) : σ :=
  if h : ext.idx < exts.size then
    let s : EnvExtensionState := exts[ext.idx]
    unsafeCast s
  else
    panic! invalidExtMsg

unsafe def registerExt {σ} (mkInitial : IO σ) : IO (Ext σ) := do
  unless (← initializing) do
    throw (IO.userError "failed to register environment, extensions can only be registered during initialization")
  let exts ← envExtensionsRef.get
  let idx := exts.size
  let ext : Ext σ := {
     idx        := idx,
     mkInitial  := mkInitial,
  }
  envExtensionsRef.modify fun exts => exts.push (unsafeCast ext)
  pure ext

def mkInitialExtStates : IO (Array EnvExtensionState) := do
  let exts ← envExtensionsRef.get
  exts.mapM fun ext => ext.mkInitial

unsafe def imp : EnvExtensionInterface := {
  ext                  := Ext
  ensureExtensionsSize := ensureExtensionsArraySize
  inhabitedExt         := fun _ => ⟨default⟩
  registerExt          := registerExt
  setState             := setState
  modifyState          := modifyState
  getState             := getState
  mkInitialExtStates   := mkInitialExtStates
}

end EnvExtensionInterfaceUnsafe

@[implemented_by EnvExtensionInterfaceUnsafe.imp]
opaque EnvExtensionInterfaceImp : EnvExtensionInterface

def EnvExtension (σ : Type) : Type := EnvExtensionInterfaceImp.ext σ

private def ensureExtensionsArraySize (env : Environment) : IO Environment := do
  let exts ← EnvExtensionInterfaceImp.ensureExtensionsSize env.checked.get.extensions
  return env.modifyCheckedAsync ({ · with extensions := exts })

namespace EnvExtension
instance {σ} [s : Inhabited σ] : Inhabited (EnvExtension σ) := EnvExtensionInterfaceImp.inhabitedExt s

def setState {σ : Type} (ext : EnvExtension σ) (env : Environment) (s : σ) : Environment :=
  let checked := env.checked.get
  env.setCheckedSync { checked with extensions := EnvExtensionInterfaceImp.setState ext checked.extensions s }

def modifyState {σ : Type} (ext : EnvExtension σ) (env : Environment) (f : σ → σ) : Environment :=
  let checked := env.checked.get
  env.setCheckedSync { checked with extensions := EnvExtensionInterfaceImp.modifyState ext checked.extensions f }

def getState {σ : Type} [Inhabited σ] (ext : EnvExtension σ) (env : Environment) : σ :=
  EnvExtensionInterfaceImp.getState ext env.checked.get.extensions

end EnvExtension

/-- Environment extensions can only be registered during initialization.
   Reasons:
   1- Our implementation assumes the number of extensions does not change after an environment object is created.
   2- We do not use any synchronization primitive to access `envExtensionsRef`.

   Note that by default, extension state is *not* stored in .olean files and will not propagate across `import`s.
   For that, you need to register a persistent environment extension. -/
def registerEnvExtension {σ : Type} (mkInitial : IO σ) : IO (EnvExtension σ) := EnvExtensionInterfaceImp.registerExt mkInitial
private def mkInitialExtensionStates : IO (Array EnvExtensionState) := EnvExtensionInterfaceImp.mkInitialExtStates

@[export lean_mk_empty_environment]
def mkEmptyEnvironment (trustLevel : UInt32 := 0) : IO Environment := do
  let initializing ← IO.initializing
  if initializing then throw (IO.userError "environment objects cannot be created during initialization")
  let exts ← mkInitialExtensionStates
  pure {
    checkedWithoutAsync := {
      const2ModIdx    := {}
      constants       := {}
      header          := { trustLevel }
      extraConstNames := {}
      extensions      := exts
    }
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
  (ext.toEnvExtension.getState env).importedEntries.get! m

def addEntry {α β σ : Type} (ext : PersistentEnvExtension α β σ) (env : Environment) (b : β) : Environment :=
  ext.toEnvExtension.modifyState env fun s =>
    let state   := ext.addEntryFn s.state b;
    { s with state := state }

/-- Get the current state of the given extension in the given environment. -/
def getState {α β σ : Type} [Inhabited σ] (ext : PersistentEnvExtension α β σ) (env : Environment) : σ :=
  (ext.toEnvExtension.getState env).state

/-- Set the current state of the given extension in the given environment. -/
def setState {α β σ : Type} (ext : PersistentEnvExtension α β σ) (env : Environment) (s : σ) : Environment :=
  ext.toEnvExtension.modifyState env fun ps => { ps with  state := s }

/-- Modify the state of the given extension in the given environment by applying the given function. -/
def modifyState {α β σ : Type} (ext : PersistentEnvExtension α β σ) (env : Environment) (f : σ → σ) : Environment :=
  ext.toEnvExtension.modifyState env fun ps => { ps with state := f (ps.state) }

end PersistentEnvExtension

builtin_initialize persistentEnvExtensionsRef : IO.Ref (Array (PersistentEnvExtension EnvExtensionEntry EnvExtensionEntry EnvExtensionState)) ← IO.mkRef #[]

structure PersistentEnvExtensionDescr (α β σ : Type) where
  name            : Name := by exact decl_name%
  mkInitial       : IO σ
  addImportedFn   : Array (Array α) → ImportM σ
  addEntryFn      : σ → β → σ
  exportEntriesFn : σ → Array α
  statsFn         : σ → Format := fun _ => Format.nil

unsafe def registerPersistentEnvExtensionUnsafe {α β σ : Type} [Inhabited σ] (descr : PersistentEnvExtensionDescr α β σ) : IO (PersistentEnvExtension α β σ) := do
  let pExts ← persistentEnvExtensionsRef.get
  if pExts.any (fun ext => ext.name == descr.name) then throw (IO.userError s!"invalid environment extension, '{descr.name}' has already been used")
  let ext ← registerEnvExtension do
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

def registerSimplePersistentEnvExtension {α σ : Type} [Inhabited σ] (descr : SimplePersistentEnvExtensionDescr α σ) : IO (SimplePersistentEnvExtension α σ) :=
  registerPersistentEnvExtension {
    name            := descr.name,
    mkInitial       := pure ([], descr.addImportedFn #[]),
    addImportedFn   := fun as => pure ([], descr.addImportedFn as),
    addEntryFn      := fun s e => match s with
      | (entries, s) => (e::entries, descr.addEntryFn s e),
    exportEntriesFn := fun s => descr.toArrayFn s.1.reverse,
    statsFn := fun s => format "number of local entries: " ++ format s.1.length
  }

namespace SimplePersistentEnvExtension

instance {α σ : Type} [Inhabited σ] : Inhabited (SimplePersistentEnvExtension α σ) :=
  inferInstanceAs (Inhabited (PersistentEnvExtension α α (List α × σ)))

/-- Get the list of values used to update the state of the given
`SimplePersistentEnvExtension` in the current file. -/
def getEntries {α σ : Type} [Inhabited σ] (ext : SimplePersistentEnvExtension α σ) (env : Environment) : List α :=
  (PersistentEnvExtension.getState ext env).1

/-- Get the current state of the given `SimplePersistentEnvExtension`. -/
def getState {α σ : Type} [Inhabited σ] (ext : SimplePersistentEnvExtension α σ) (env : Environment) : σ :=
  (PersistentEnvExtension.getState ext env).2

/-- Set the current state of the given `SimplePersistentEnvExtension`. This change is *not* persisted across files. -/
def setState {α σ : Type} (ext : SimplePersistentEnvExtension α σ) (env : Environment) (s : σ) : Environment :=
  PersistentEnvExtension.modifyState ext env (fun ⟨entries, _⟩ => (entries, s))

/-- Modify the state of the given extension in the given environment by applying the given function. This change is *not* persisted across files. -/
def modifyState {α σ : Type} (ext : SimplePersistentEnvExtension α σ) (env : Environment) (f : σ → σ) : Environment :=
  PersistentEnvExtension.modifyState ext env (fun ⟨entries, s⟩ => (entries, f s))

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
  }

namespace TagDeclarationExtension

instance : Inhabited TagDeclarationExtension :=
  inferInstanceAs (Inhabited (SimplePersistentEnvExtension Name NameSet))

def tag (ext : TagDeclarationExtension) (env : Environment) (declName : Name) : Environment :=
  have : Inhabited Environment := ⟨env⟩
  assert! env.getModuleIdxFor? declName |>.isNone -- See comment at `TagDeclarationExtension`
  ext.addEntry env declName

def isTagged (ext : TagDeclarationExtension) (env : Environment) (declName : Name) : Bool :=
  match env.getModuleIdxFor? declName with
  | some modIdx => (ext.getModuleEntries env modIdx).binSearchContains declName Name.quickLt
  | none        => (ext.getState env).contains declName

end TagDeclarationExtension

/-- Environment extension for mapping declarations to values.
    Declarations must only be inserted into the mapping in the module where they were declared. -/

def MapDeclarationExtension (α : Type) := PersistentEnvExtension (Name × α) (Name × α) (NameMap α)

def mkMapDeclarationExtension (name : Name := by exact decl_name%) : IO (MapDeclarationExtension α) :=
  registerPersistentEnvExtension {
    name            := name,
    mkInitial       := pure {}
    addImportedFn   := fun _ => pure {}
    addEntryFn      := fun s (n, v) => s.insert n v
    exportEntriesFn := fun s => s.toArray
  }

namespace MapDeclarationExtension

instance : Inhabited (MapDeclarationExtension α) :=
  inferInstanceAs (Inhabited (PersistentEnvExtension ..))

def insert (ext : MapDeclarationExtension α) (env : Environment) (declName : Name) (val : α) : Environment :=
  have : Inhabited Environment := ⟨env⟩
  assert! env.getModuleIdxFor? declName |>.isNone -- See comment at `MapDeclarationExtension`
  ext.addEntry env (declName, val)

def find? [Inhabited α] (ext : MapDeclarationExtension α) (env : Environment) (declName : Name) : Option α :=
  match env.getModuleIdxFor? declName with
  | some modIdx =>
    match (ext.getModuleEntries env modIdx).binSearch (declName, default) (fun a b => Name.quickLt a.1 b.1) with
    | some e => some e.2
    | none   => none
  | none => (ext.getState env).find? declName

def contains [Inhabited α] (ext : MapDeclarationExtension α) (env : Environment) (declName : Name) : Bool :=
  match env.getModuleIdxFor? declName with
  | some modIdx => (ext.getModuleEntries env modIdx).binSearchContains (declName, default) (fun a b => Name.quickLt a.1 b.1)
  | none        => (ext.getState env).contains declName

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
  let entries := pExts.map fun pExt =>
    let state := pExt.getState env
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
  let mut env := env
  let extDescrs ← persistentEnvExtensionsRef.get
  /- For extensions starting at `startingAt`, ensure their `importedEntries` array have size `mods.size`. -/
  for extDescr in extDescrs[startingAt:] do
    env := extDescr.toEnvExtension.modifyState env fun s => { s with importedEntries := mkArray mods.size #[] }
  /- For each module `mod`, and `mod.entries`, if the extension name is one of the extensions after `startingAt`, set `entries` -/
  let extNameIdx ← mkExtNameMap startingAt
  for h : modIdx in [:mods.size] do
    let mod := mods[modIdx]
    for (extName, entries) in mod.entries do
      if let some entryIdx := extNameIdx[extName]? then
        env := extDescrs[entryIdx]!.toEnvExtension.modifyState env fun s => { s with importedEntries := s.importedEntries.set! modIdx entries }
  return env

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

private partial def finalizePersistentExtensions (env : Environment) (mods : Array ModuleData) (opts : Options) : IO Environment := do
  loop 0 env
where
  loop (i : Nat) (env : Environment) : IO Environment := do
    -- Recall that the size of the array stored `persistentEnvExtensionRef` may increase when we import user-defined environment extensions.
    let pExtDescrs ← persistentEnvExtensionsRef.get
    if h : i < pExtDescrs.size then
      let extDescr := pExtDescrs[i]
      let s := extDescr.toEnvExtension.getState env
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
    checkedWithoutAsync := {
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
    (leakEnv := false) : IO Environment := profileitIO "import" opts do
  for imp in imports do
    if imp.module matches .anonymous then
      throw <| IO.userError "import failed, trying to import module with anonymous name"
  withImporting do
    let (_, s) ← importModulesCore imports |>.run
    finalizeImport (leakEnv := leakEnv) s imports opts trustLevel

/--
  Create environment object from imports and free compacted regions after calling `act`. No live references to the
  environment object or imported objects may exist after `act` finishes. -/
unsafe def withImportModules {α : Type} (imports : Array Import) (opts : Options) (trustLevel : UInt32 := 0) (act : Environment → IO α) : IO α := do
  let env ← importModules imports opts trustLevel
  try act env finally env.freeRegions

/--
Environment extension for tracking all `namespace` declared by users.
-/
builtin_initialize namespacesExt : SimplePersistentEnvExtension Name NameSSet ←
  registerSimplePersistentEnvExtension {
    addImportedFn   := fun as =>
      /-
      We compute a `HashMap Name Unit` and then convert to `NameSSet` to improve Lean startup time.
      Note: we have used `perf` to profile Lean startup cost when processing a file containing just `import Lean`.
      6.18% of the runtime is here. It was 9.31% before the `HashMap` optimization.
      -/
      let capacity := as.foldl (init := 0) fun r e => r + e.size
      let map : Std.HashMap Name Unit := Std.HashMap.empty capacity
      let map := mkStateFromImportedEntries (fun map name => map.insert name ()) map as
      SMap.fromHashMap map |>.switch
    addEntryFn      := fun s n => s.insert n
  }

@[inherit_doc Kernel.Environment.enableDiag]
def Kernel.enableDiag (env : Lean.Environment) (flag : Bool) : Lean.Environment :=
  env.modifyCheckedAsync (·.enableDiag flag)

def Kernel.isDiagnosticsEnabled (env : Lean.Environment) : Bool :=
  env.checkedWithoutAsync.isDiagnosticsEnabled

def Kernel.resetDiag (env : Lean.Environment) : Lean.Environment :=
  env.modifyCheckedAsync (·.resetDiag)

def Kernel.getDiagnostics (env : Lean.Environment) : Diagnostics :=
  env.checked.get.diagnostics

def Kernel.setDiagnostics (env : Lean.Environment) (diag : Diagnostics) : Lean.Environment :=
  env.modifyCheckedAsync (·.setDiagnostics diag)

namespace Environment

/-- Register a new namespace in the environment. -/
def registerNamespace (env : Environment) (n : Name) : Environment :=
  if (namespacesExt.getState env).contains n then env else namespacesExt.addEntry env n

/-- Return `true` if `n` is the name of a namespace in `env`. -/
def isNamespace (env : Environment) (n : Name) : Bool :=
  (namespacesExt.getState env).contains n

/-- Return a set containing all namespaces in `env`. -/
def getNamespaceSet (env : Environment) : NameSSet :=
  namespacesExt.getState env

@[export lean_elab_environment_update_base_after_kernel_add]
private def updateBaseAfterKernelAdd (env : Environment) (kernel : Kernel.Environment) : Environment :=
  env.setCheckedSync kernel

@[export lean_display_stats]
def displayStats (env : Environment) : IO Unit := do
  let pExtDescrs ← persistentEnvExtensionsRef.get
  IO.println ("direct imports:                        " ++ toString env.header.imports);
  IO.println ("number of imported modules:            " ++ toString env.header.regions.size);
  IO.println ("number of memory-mapped modules:       " ++ toString (env.header.regions.filter (·.isMemoryMapped) |>.size));
  IO.println ("number of buckets for imported consts: " ++ toString env.constants.numBuckets);
  IO.println ("trust level:                           " ++ toString env.header.trustLevel);
  IO.println ("number of extensions:                  " ++ toString env.checkedWithoutAsync.extensions.size);
  pExtDescrs.forM fun extDescr => do
    IO.println ("extension '" ++ toString extDescr.name ++ "'")
    let s := extDescr.toEnvExtension.getState env
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

end Lean
