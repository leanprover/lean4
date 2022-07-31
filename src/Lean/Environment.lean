/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Std.Data.HashMap
import Lean.ImportingFlag
import Lean.Data.SMap
import Lean.Declaration
import Lean.LocalContext
import Lean.Util.Path
import Lean.Util.FindExpr
import Lean.Util.Profile

namespace Lean
/-- Opaque environment extension state. -/
opaque EnvExtensionStateSpec : (α : Type) × Inhabited α := ⟨Unit, ⟨()⟩⟩
def EnvExtensionState : Type := EnvExtensionStateSpec.fst
instance : Inhabited EnvExtensionState := EnvExtensionStateSpec.snd

def ModuleIdx := Nat
abbrev ModuleIdx.toNat (midx : ModuleIdx) : Nat := midx

instance : Inhabited ModuleIdx := inferInstanceAs (Inhabited Nat)

abbrev ConstMap := SMap Name ConstantInfo

structure Import where
  module      : Name
  runtimeOnly : Bool := false

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
  imports    : Array Import
  constants  : Array ConstantInfo
  entries    : Array (Name × Array EnvExtensionEntry)
  deriving Inhabited

/-- Environment fields that are not used often. -/
structure EnvironmentHeader where
  /--
  The trust level used by the kernel. For example,
  the kernel assumes imported constants are type correct when the trust level is greater than zero.
  -/
  trustLevel   : UInt32       := 0
  /--
  `quotInit = true` if the command `init_quot` has already been executed for the environment, and
  `Quot` declarations have been added to the environment.
  -/
  quotInit     : Bool         := false
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
  deriving Inhabited

open Std (HashMap)

/--
An environment stores declarations provided by the user. The kernel
currently supports different kinds of declarations such as definitions, theorems,
and inductive families. Each has a unique identifier (i.e., `Name`), and can be
parameterized by a sequence of universe parameters.
A constant in Lean is just a reference to a `ConstantInfo` object. The main task of
the kernel is to type check these declarations and refuse type incorrect ones. The
kernel does not allow declarations containing metavariables and/or free variables
to be added to an environment. Environments are never destructively updated.

The environment also contains a collction of extensions. For example, the `simp` theorems
declared by users are stored in an environment extension. Users can declare new extensions
using meta-programming.
-/
structure Environment where
  /--
  Mapping from constant name to module (index) where constant has been declared.
  Recall that a Leah file has a header where previously compiled modules can be imported.
  Each imported module has a unique `ModuleIdx`.
  Many extensions use the `ModuleIdx` to efficiently retrieve information stored in imported modules.
  -/
  const2ModIdx : HashMap Name ModuleIdx
  /--
  Mapping from constant name to `ConstantInfo`. It contains all constants (definitions, theorems, axioms, etc)
  that have been already type checked by the kernel.
  -/
  constants    : ConstMap
  /--
  Environment extensions. It also includes user-defined extensions.
  -/
  extensions   : Array EnvExtensionState
  /-- The header contains additional information that is not updated often. -/
  header       : EnvironmentHeader := {}
  deriving Inhabited

namespace Environment

def addAux (env : Environment) (cinfo : ConstantInfo) : Environment :=
  { env with constants := env.constants.insert cinfo.name cinfo }

@[export lean_environment_find]
def find? (env : Environment) (n : Name) : Option ConstantInfo :=
  /- It is safe to use `find'` because we never overwrite imported declarations. -/
  env.constants.find?' n

def contains (env : Environment) (n : Name) : Bool :=
  env.constants.contains n

def imports (env : Environment) : Array Import :=
  env.header.imports

def allImportedModuleNames (env : Environment) : Array Name :=
  env.header.moduleNames

@[export lean_environment_set_main_module]
def setMainModule (env : Environment) (m : Name) : Environment :=
  { env with header := { env.header with mainModule := m } }

@[export lean_environment_main_module]
def mainModule (env : Environment) : Name :=
  env.header.mainModule

@[export lean_environment_mark_quot_init]
private def markQuotInit (env : Environment) : Environment :=
  { env with header := { env.header with quotInit := true } }

@[export lean_environment_quot_init]
private def isQuotInit (env : Environment) : Bool :=
  env.header.quotInit

@[export lean_environment_trust_level]
private def getTrustLevel (env : Environment) : UInt32 :=
  env.header.trustLevel

def getModuleIdxFor? (env : Environment) (declName : Name) : Option ModuleIdx :=
  env.const2ModIdx.find? declName

def isConstructor (env : Environment) (declName : Name) : Bool :=
  match env.find? declName with
  | ConstantInfo.ctorInfo _ => true
  | _                       => false

def getModuleIdx? (env : Environment) (moduleName : Name) : Option ModuleIdx :=
  env.header.moduleNames.findIdx? (· == moduleName)

end Environment

/-- Exceptions that can be raised by the Kernel when type checking new declarations. -/
inductive KernelException where
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
  | other            (msg : String)

namespace Environment

/-- Type check given declaration and add it to the environment -/
@[extern "lean_add_decl"]
opaque addDecl (env : Environment) (decl : @& Declaration) : Except KernelException Environment

end Environment

/-- Interface for managing environment extensions. -/
structure EnvExtensionInterface where
  ext              : Type → Type
  inhabitedExt {σ} : Inhabited σ → Inhabited (ext σ)
  registerExt  {σ} (mkInitial : IO σ) : IO (ext σ)
  setState     {σ} (e : ext σ) (env : Environment) : σ → Environment
  modifyState  {σ} (e : ext σ) (env : Environment) : (σ → σ) → Environment
  getState     {σ} [Inhabited σ] (e : ext σ) (env : Environment) : σ
  mkInitialExtStates : IO (Array EnvExtensionState)
  ensureExtensionsSize : Environment → IO Environment

instance : Inhabited EnvExtensionInterface where
  default := {
    ext                  := id
    inhabitedExt         := id
    ensureExtensionsSize := fun env => pure env
    registerExt          := fun mk => mk
    setState             := fun _ env _ => env
    modifyState          := fun _ env _ => env
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
partial def ensureExtensionsArraySize (env : Environment) : IO Environment := do
  loop env.extensions.size env
where
  loop (i : Nat) (env : Environment) : IO Environment := do
    let envExtensions ← envExtensionsRef.get
    if i < envExtensions.size then
      let s ← envExtensions[i]!.mkInitial
      let env := { env with extensions := env.extensions.push s }
      loop (i + 1) env
    else
      return env

private def invalidExtMsg := "invalid environment extension has been accessed"

unsafe def setState {σ} (ext : Ext σ) (env : Environment) (s : σ) : Environment :=
  if h : ext.idx < env.extensions.size then
    { env with extensions := env.extensions.set ⟨ext.idx, h⟩ (unsafeCast s) }
  else
    panic! invalidExtMsg

@[inline] unsafe def modifyState {σ : Type} (ext : Ext σ) (env : Environment) (f : σ → σ) : Environment :=
  if ext.idx < env.extensions.size then
    { env with
      extensions := env.extensions.modify ext.idx fun s =>
        let s : σ := unsafeCast s
        let s : σ := f s
        unsafeCast s }
  else
    panic! invalidExtMsg

unsafe def getState {σ} [Inhabited σ] (ext : Ext σ) (env : Environment) : σ :=
  if h : ext.idx < env.extensions.size then
    let s : EnvExtensionState := env.extensions.get ⟨ext.idx, h⟩
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

@[implementedBy EnvExtensionInterfaceUnsafe.imp]
opaque EnvExtensionInterfaceImp : EnvExtensionInterface

def EnvExtension (σ : Type) : Type := EnvExtensionInterfaceImp.ext σ

private def ensureExtensionsArraySize (env : Environment) : IO Environment :=
  EnvExtensionInterfaceImp.ensureExtensionsSize env

namespace EnvExtension
instance {σ} [s : Inhabited σ] : Inhabited (EnvExtension σ) := EnvExtensionInterfaceImp.inhabitedExt s
def setState {σ : Type} (ext : EnvExtension σ) (env : Environment) (s : σ) : Environment := EnvExtensionInterfaceImp.setState ext env s
def modifyState {σ : Type} (ext : EnvExtension σ) (env : Environment) (f : σ → σ) : Environment := EnvExtensionInterfaceImp.modifyState ext env f
def getState {σ : Type} [Inhabited σ] (ext : EnvExtension σ) (env : Environment) : σ := EnvExtensionInterfaceImp.getState ext env
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
    const2ModIdx := {},
    constants    := {},
    header       := { trustLevel := trustLevel },
    extensions   := exts
  }

structure PersistentEnvExtensionState (α : Type) (σ : Type) where
  importedEntries : Array (Array α)  -- entries per imported module
  state : σ

structure ImportM.Context where
  env  : Environment
  opts : Options

abbrev ImportM := ReaderT Lean.ImportM.Context IO

/-- An environment extension with support for storing/retrieving entries from a .olean file.
   - α is the type of the entries that are stored in .olean files.
   - β is the type of values used to update the state.
   - σ is the actual state.

   Remark: for most extensions α and β coincide.

   Note that `addEntryFn` is not in `IO`. This is intentional, and allows us to write simple functions such as
   ```
   def addAlias (env : Environment) (a : Name) (e : Name) : Environment :=
   aliasExtension.addEntry env (a, e)
   ```
   without using `IO`. We have many functions like `addAlias`.

   `α` and ‵β` do not coincide for extensions where the data used to update the state contains, for example,
   closures which we currently cannot store in files. -/
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

def getState {α β σ : Type} [Inhabited σ] (ext : PersistentEnvExtension α β σ) (env : Environment) : σ :=
  (ext.toEnvExtension.getState env).state

def setState {α β σ : Type} (ext : PersistentEnvExtension α β σ) (env : Environment) (s : σ) : Environment :=
  ext.toEnvExtension.modifyState env fun ps => { ps with  state := s }

def modifyState {α β σ : Type} (ext : PersistentEnvExtension α β σ) (env : Environment) (f : σ → σ) : Environment :=
  ext.toEnvExtension.modifyState env fun ps => { ps with state := f (ps.state) }

end PersistentEnvExtension

builtin_initialize persistentEnvExtensionsRef : IO.Ref (Array (PersistentEnvExtension EnvExtensionEntry EnvExtensionEntry EnvExtensionState)) ← IO.mkRef #[]

structure PersistentEnvExtensionDescr (α β σ : Type) where
  name            : Name
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

@[implementedBy registerPersistentEnvExtensionUnsafe]
opaque registerPersistentEnvExtension {α β σ : Type} [Inhabited σ] (descr : PersistentEnvExtensionDescr α β σ) : IO (PersistentEnvExtension α β σ)

/-- Simple `PersistentEnvExtension` that implements `exportEntriesFn` using a list of entries. -/
def SimplePersistentEnvExtension (α σ : Type) := PersistentEnvExtension α α (List α × σ)

@[specialize] def mkStateFromImportedEntries {α σ : Type} (addEntryFn : σ → α → σ) (initState : σ) (as : Array (Array α)) : σ :=
  as.foldl (fun r es => es.foldl (fun r e => addEntryFn r e) r) initState

structure SimplePersistentEnvExtensionDescr (α σ : Type) where
  name          : Name
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

def getEntries {α σ : Type} [Inhabited σ] (ext : SimplePersistentEnvExtension α σ) (env : Environment) : List α :=
  (PersistentEnvExtension.getState ext env).1

def getState {α σ : Type} [Inhabited σ] (ext : SimplePersistentEnvExtension α σ) (env : Environment) : σ :=
  (PersistentEnvExtension.getState ext env).2

def setState {α σ : Type} (ext : SimplePersistentEnvExtension α σ) (env : Environment) (s : σ) : Environment :=
  PersistentEnvExtension.modifyState ext env (fun ⟨entries, _⟩ => (entries, s))

def modifyState {α σ : Type} (ext : SimplePersistentEnvExtension α σ) (env : Environment) (f : σ → σ) : Environment :=
  PersistentEnvExtension.modifyState ext env (fun ⟨entries, s⟩ => (entries, f s))

end SimplePersistentEnvExtension

/-- Environment extension for tagging declarations.
    Declarations must only be tagged in the module where they were declared. -/
def TagDeclarationExtension := SimplePersistentEnvExtension Name NameSet

def mkTagDeclarationExtension (name : Name) : IO TagDeclarationExtension :=
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
  assert! env.getModuleIdxFor? declName |>.isNone -- See comment at `TagDeclarationExtension`
  ext.addEntry env declName

def isTagged (ext : TagDeclarationExtension) (env : Environment) (declName : Name) : Bool :=
  match env.getModuleIdxFor? declName with
  | some modIdx => (ext.getModuleEntries env modIdx).binSearchContains declName Name.quickLt
  | none        => (ext.getState env).contains declName

end TagDeclarationExtension

/-- Environment extension for mapping declarations to values.
    Declarations must only be inserted into the mapping in the module where they were declared. -/

def MapDeclarationExtension (α : Type) := SimplePersistentEnvExtension (Name × α) (NameMap α)

def mkMapDeclarationExtension [Inhabited α] (name : Name) : IO (MapDeclarationExtension α) :=
  registerSimplePersistentEnvExtension {
    name          := name,
    addImportedFn := fun _ => {},
    addEntryFn    := fun s n => s.insert n.1 n.2 ,
    toArrayFn     := fun es => es.toArray.qsort (fun a b => Name.quickLt a.1 b.1)
  }

namespace MapDeclarationExtension

instance : Inhabited (MapDeclarationExtension α) :=
  inferInstanceAs (Inhabited (SimplePersistentEnvExtension ..))

def insert (ext : MapDeclarationExtension α) (env : Environment) (declName : Name) (val : α) : Environment :=
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
  let entries : Array (Name × Array EnvExtensionEntry) := pExts.size.fold
    (fun i result =>
      let state  := (pExts.get! i).getState env
      let exportEntriesFn := (pExts.get! i).exportEntriesFn
      let extName    := (pExts.get! i).name
      result.push (extName, exportEntriesFn state))
    #[]
  pure {
    imports    := env.header.imports,
    constants  := env.constants.foldStage2 (fun cs _ c => cs.push c) #[],
    entries    := entries
  }

@[export lean_write_module]
def writeModule (env : Environment) (fname : System.FilePath) : IO Unit := do
  saveModuleData fname env.mainModule (← mkModuleData env)

private partial def getEntriesFor (mod : ModuleData) (extId : Name) (i : Nat) : Array EnvExtensionEntry :=
  if i < mod.entries.size then
    let curr := mod.entries.get! i;
    if curr.1 == extId then curr.2 else getEntriesFor mod extId (i+1)
  else
    #[]

private def setImportedEntries (env : Environment) (mods : Array ModuleData) (startingAt : Nat := 0) : IO Environment := do
  let mut env := env
  let pExtDescrs ← persistentEnvExtensionsRef.get
  for mod in mods do
    for extDescr in pExtDescrs[startingAt:] do
      let entries := getEntriesFor mod extDescr.name 0
      env := extDescr.toEnvExtension.modifyState env fun s => { s with importedEntries := s.importedEntries.push entries }
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
@[extern 1 "lean_get_num_attributes"] opaque getNumBuiltiAttributes : IO Nat

private partial def finalizePersistentExtensions (env : Environment) (mods : Array ModuleData) (opts : Options) : IO Environment := do
  loop 0 env
where
  loop (i : Nat) (env : Environment) : IO Environment := do
    -- Recall that the size of the array stored `persistentEnvExtensionRef` may increase when we import user-defined environment extensions.
    let pExtDescrs ← persistentEnvExtensionsRef.get
    if i < pExtDescrs.size then
      let extDescr := pExtDescrs[i]!
      let s := extDescr.toEnvExtension.getState env
      let prevSize := (← persistentEnvExtensionsRef.get).size
      let prevAttrSize ← getNumBuiltiAttributes
      let newState ← extDescr.addImportedFn s.importedEntries { env := env, opts := opts }
      let mut env := extDescr.toEnvExtension.setState env { s with state := newState }
      env ← ensureExtensionsArraySize env
      if (← persistentEnvExtensionsRef.get).size > prevSize || (← getNumBuiltiAttributes) > prevAttrSize then
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
  moduleNameSet : NameSet := {}
  moduleNames   : Array Name := #[]
  moduleData    : Array ModuleData := #[]
  regions       : Array CompactedRegion := #[]

@[export lean_import_modules]
partial def importModules (imports : List Import) (opts : Options) (trustLevel : UInt32 := 0) : IO Environment := profileitIO "import" opts do
  for imp in imports do
    if imp.module matches .anonymous then
      throw <| IO.userError "import failed, trying to import module with anonymous name"
  withImporting do
    let (_, s) ← importMods imports |>.run {}
    let mut numConsts := 0
    for mod in s.moduleData do
      numConsts := numConsts + mod.constants.size
    let mut modIdx : Nat := 0
    let mut const2ModIdx : HashMap Name ModuleIdx := Std.mkHashMap (capacity := numConsts)
    let mut constantMap : HashMap Name ConstantInfo := Std.mkHashMap (capacity := numConsts)
    for mod in s.moduleData do
      for cinfo in mod.constants do
        const2ModIdx := const2ModIdx.insert cinfo.name modIdx
        match constantMap.insert' cinfo.name cinfo with
        | (constantMap', replaced) =>
          constantMap := constantMap'
          if replaced then throw (IO.userError s!"import failed, environment already contains '{cinfo.name}'")
       modIdx := modIdx + 1
    let constants : ConstMap := SMap.fromHashMap constantMap false
    let exts ← mkInitialExtensionStates
    let env : Environment := {
      const2ModIdx := const2ModIdx,
      constants    := constants,
      extensions   := exts,
      header       := {
        quotInit     := !imports.isEmpty, -- We assume `core.lean` initializes quotient module
        trustLevel   := trustLevel,
        imports      := imports.toArray,
        regions      := s.regions,
        moduleNames  := s.moduleNames
        moduleData   := s.moduleData
      }
    }
    let env ← setImportedEntries env s.moduleData
    let env ← finalizePersistentExtensions env s.moduleData opts
    pure env
where
  importMods : List Import → StateRefT ImportState IO Unit
  | []    => pure ()
  | i::is => do
    if i.runtimeOnly || (← get).moduleNameSet.contains i.module then
      importMods is
    else do
      modify fun s => { s with moduleNameSet := s.moduleNameSet.insert i.module }
      let mFile ← findOLean i.module
      unless (← mFile.pathExists) do
        throw <| IO.userError s!"object file '{mFile}' of module {i.module} does not exist"
      let (mod, region) ← readModuleData mFile
      importMods mod.imports.toList
      modify fun s => { s with
        moduleData  := s.moduleData.push mod
        regions     := s.regions.push region
        moduleNames := s.moduleNames.push i.module
      }
      importMods is

/--
  Create environment object from imports and free compacted regions after calling `act`. No live references to the
  environment object or imported objects may exist after `act` finishes. -/
unsafe def withImportModules {α : Type} (imports : List Import) (opts : Options) (trustLevel : UInt32 := 0) (x : Environment → IO α) : IO α := do
  let env ← importModules imports opts trustLevel
  try x env finally env.freeRegions

/--
Environment extension for tracking all `namespace` declared by users.
-/
builtin_initialize namespacesExt : SimplePersistentEnvExtension Name NameSSet ←
  registerSimplePersistentEnvExtension {
    name            := `namespaces,
    addImportedFn   := fun as => mkStateFromImportedEntries NameSSet.insert NameSSet.empty as |>.switch,
    addEntryFn      := fun s n => s.insert n
  }

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

private def isNamespaceName : Name → Bool
  | .str .anonymous _ => true
  | .str p _          => isNamespaceName p
  | _                 => false

private def registerNamePrefixes : Environment → Name → Environment
  | env, .str p _ => if isNamespaceName p then registerNamePrefixes (registerNamespace env p) p else env
  | env, _        => env

@[export lean_environment_add]
def add (env : Environment) (cinfo : ConstantInfo) : Environment :=
  let env := registerNamePrefixes env cinfo.name
  env.addAux cinfo

@[export lean_display_stats]
def displayStats (env : Environment) : IO Unit := do
  let pExtDescrs ← persistentEnvExtensionsRef.get
  IO.println ("direct imports:                        " ++ toString env.header.imports);
  IO.println ("number of imported modules:            " ++ toString env.header.regions.size);
  IO.println ("number of memory-mapped modules:       " ++ toString (env.header.regions.filter (·.isMemoryMapped) |>.size));
  IO.println ("number of consts:                      " ++ toString env.constants.size);
  IO.println ("number of imported consts:             " ++ toString env.constants.stageSizes.1);
  IO.println ("number of local consts:                " ++ toString env.constants.stageSizes.2);
  IO.println ("number of buckets for imported consts: " ++ toString env.constants.numBuckets);
  IO.println ("trust level:                           " ++ toString env.header.trustLevel);
  IO.println ("number of extensions:                  " ++ toString env.extensions.size);
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
  Recall that the Kernel type checker does not support metavariables.
  When implementing automation, consider using the `MetaM` methods. -/
@[extern "lean_kernel_is_def_eq"]
opaque isDefEq (env : Environment) (lctx : LocalContext) (a b : Expr) : Bool

/--
  Kernel WHNF function. We use it mainly for debugging purposes.
  Recall that the Kernel type checker does not support metavariables.
  When implementing automation, consider using the `MetaM` methods. -/
@[extern "lean_kernel_whnf"]
opaque whnf (env : Environment) (lctx : LocalContext) (a : Expr) : Expr

end Kernel

class MonadEnv (m : Type → Type) where
  getEnv    : m Environment
  modifyEnv : (Environment → Environment) → m Unit

export MonadEnv (getEnv modifyEnv)

instance (m n) [MonadLift m n] [MonadEnv m] : MonadEnv n where
  getEnv    := liftM (getEnv : m Environment)
  modifyEnv := fun f => liftM (modifyEnv f : m Unit)

end Lean
