/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Std.Data.HashMap
import Lean.Data.SMap
import Lean.Declaration
import Lean.LocalContext
import Lean.Util.Path
import Lean.Util.FindExpr

namespace Lean
/- Opaque environment extension state. It is essentially the Lean version of a C `void *` -/
def EnvExtensionState : Type := NonScalar

instance EnvExtensionState.inhabited : Inhabited EnvExtensionState := inferInstanceAs (Inhabited NonScalar)

def ModuleIdx := Nat

instance ModuleIdx.inhabited : Inhabited ModuleIdx := inferInstanceAs (Inhabited Nat)

abbrev ConstMap := SMap Name ConstantInfo

structure Import :=
(module      : Name)
(runtimeOnly : Bool := false)

instance : HasToString Import :=
⟨fun imp => toString imp.module ++ if imp.runtimeOnly then " (runtime)" else ""⟩

/--
  A compacted region holds multiple Lean objects in a contiguous memory region, which can be read/written to/from disk.
  Objects inside the region do not have reference counters and cannot be freed individually. The contents of .olean
  files are compacted regions. -/
def CompactedRegion := USize

/-- Free a compacted region and its contents. No live references to the contents may exist at the time of invocation. -/
@[extern 2 "lean_compacted_region_free"]
unsafe constant CompactedRegion.free : CompactedRegion → IO Unit := arbitrary _

/- Environment fields that are not used often. -/
structure EnvironmentHeader :=
(trustLevel   : UInt32       := 0)
(quotInit     : Bool         := false)
(mainModule   : Name         := arbitrary _)
(imports      : Array Import := #[]) -- direct imports
(regions      : Array CompactedRegion := #[]) -- compacted regions of all imported modules
(moduleNames  : NameSet      := {})  -- names of all imported modules

open Std (HashMap)

structure Environment :=
(const2ModIdx : HashMap Name ModuleIdx)
(constants    : ConstMap)
(extensions   : Array EnvExtensionState)
(header       : EnvironmentHeader := {})

namespace Environment

instance : Inhabited Environment :=
⟨{ const2ModIdx := {}, constants := {}, extensions := #[] }⟩

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

def allImportedModuleNames (env : Environment) : NameSet :=
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

def getModuleIdxFor? (env : Environment) (c : Name) : Option ModuleIdx :=
env.const2ModIdx.find? c

def isConstructor (env : Environment) (c : Name) : Bool :=
match env.find? c with
| ConstantInfo.ctorInfo _ => true
| _                       => false

end Environment

inductive KernelException
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

/- Type check given declaration and add it to the environment -/
@[extern "lean_add_decl"]
constant addDecl (env : Environment) (decl : @& Declaration) : Except KernelException Environment := arbitrary _

/- Compile the given declaration, it assumes the declaration has already been added to the environment using `addDecl`. -/
@[extern "lean_compile_decl"]
constant compileDecl (env : Environment) (opt : @& Options) (decl : @& Declaration) : Except KernelException Environment := arbitrary _

def addAndCompile (env : Environment) (opt : Options) (decl : Declaration) : Except KernelException Environment := do
env ← addDecl env decl;
compileDecl env opt decl

end Environment

/- "Raw" environment extension. -/
structure EnvExtension (σ : Type) :=
(idx       : Nat)
(mkInitial : IO σ)
(stateInh  : σ)

namespace EnvExtension
unsafe def setStateUnsafe {σ : Type} (ext : EnvExtension σ) (env : Environment) (s : σ) : Environment :=
{ env with extensions := env.extensions.set! ext.idx (unsafeCast s) }

@[implementedBy setStateUnsafe]
constant setState {σ : Type} (ext : EnvExtension σ) (env : Environment) (s : σ) : Environment := arbitrary _

unsafe def getStateUnsafe {σ : Type} (ext : EnvExtension σ) (env : Environment) : σ :=
let s : EnvExtensionState := env.extensions.get! ext.idx;
unsafeCast s

@[implementedBy getStateUnsafe]
constant getState {σ : Type} (ext : EnvExtension σ) (env : Environment) : σ := ext.stateInh

@[inline] unsafe def modifyStateUnsafe {σ : Type} (ext : EnvExtension σ) (env : Environment) (f : σ → σ) : Environment :=
{ env with
  extensions := env.extensions.modify ext.idx $ fun s =>
    let s : σ := unsafeCast s;
    let s : σ := f s;
    unsafeCast s }

@[implementedBy modifyStateUnsafe]
constant modifyState {σ : Type} (ext : EnvExtension σ) (env : Environment) (f : σ → σ) : Environment := arbitrary _

end EnvExtension

private def mkEnvExtensionsRef : IO (IO.Ref (Array (EnvExtension EnvExtensionState))) :=
IO.mkRef #[]

@[init mkEnvExtensionsRef]
private constant envExtensionsRef : IO.Ref (Array (EnvExtension EnvExtensionState)) := arbitrary _

instance EnvExtension.Inhabited (σ : Type) [Inhabited σ] : Inhabited (EnvExtension σ) :=
⟨{ idx := 0, stateInh := arbitrary _, mkInitial := arbitrary _ }⟩

unsafe def registerEnvExtensionUnsafe {σ : Type} [Inhabited σ] (mkInitial : IO σ) : IO (EnvExtension σ) := do
initializing ← IO.initializing;
unless initializing $ throw (IO.userError ("failed to register environment, extensions can only be registered during initialization"));
exts ← envExtensionsRef.get;
let idx := exts.size;
let ext : EnvExtension σ := {
   idx        := idx,
   mkInitial  := mkInitial,
   stateInh   := arbitrary _
};
envExtensionsRef.modify (fun exts => exts.push (unsafeCast ext));
pure ext

/- Environment extensions can only be registered during initialization.
   Reasons:
   1- Our implementation assumes the number of extensions does not change after an environment object is created.
   2- We do not use any synchronization primitive to access `envExtensionsRef`. -/
@[implementedBy registerEnvExtensionUnsafe]
constant registerEnvExtension {σ : Type} [Inhabited σ] (mkInitial : IO σ) : IO (EnvExtension σ) := arbitrary _

private def mkInitialExtensionStates : IO (Array EnvExtensionState) := do
exts ← envExtensionsRef.get; exts.mapM $ fun ext => ext.mkInitial

@[export lean_mk_empty_environment]
def mkEmptyEnvironment (trustLevel : UInt32 := 0) : IO Environment := do
initializing ← IO.initializing;
when initializing $ throw (IO.userError "environment objects cannot be created during initialization");
exts ← mkInitialExtensionStates;
pure {
  const2ModIdx := {},
  constants    := {},
  header       := { trustLevel := trustLevel },
  extensions   := exts
}

structure PersistentEnvExtensionState (α : Type) (σ : Type) :=
(importedEntries : Array (Array α))  -- entries per imported module
(state : σ)

/- An environment extension with support for storing/retrieving entries from a .olean file.
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
structure PersistentEnvExtension (α : Type) (β : Type) (σ : Type) extends EnvExtension (PersistentEnvExtensionState α σ) :=
(name            : Name)
(addImportedFn   : Environment → Array (Array α) → IO σ)
(addEntryFn      : σ → β → σ)
(exportEntriesFn : σ → Array α)
(statsFn         : σ → Format)

/- Opaque persistent environment extension entry. It is essentially a C `void *`
   TODO: mark opaque -/
def EnvExtensionEntry := NonScalar

instance EnvExtensionEntry.inhabited : Inhabited EnvExtensionEntry := inferInstanceAs (Inhabited NonScalar)

instance PersistentEnvExtensionState.inhabited {α σ} [Inhabited σ] : Inhabited (PersistentEnvExtensionState α σ) :=
⟨{importedEntries := #[], state := arbitrary _ }⟩

instance PersistentEnvExtension.inhabited {α β σ} [Inhabited σ] : Inhabited (PersistentEnvExtension α β σ) :=
⟨{ toEnvExtension := { idx := 0, stateInh := arbitrary _, mkInitial := arbitrary _ },
   name := arbitrary _,
   addImportedFn := fun _ _ => arbitrary _,
   addEntryFn := fun s _ => s,
   exportEntriesFn := fun _ => #[],
   statsFn := fun _ => Format.nil }⟩

namespace PersistentEnvExtension

def getModuleEntries {α β σ : Type} (ext : PersistentEnvExtension α β σ) (env : Environment) (m : ModuleIdx) : Array α :=
(ext.toEnvExtension.getState env).importedEntries.get! m

def addEntry {α β σ : Type} (ext : PersistentEnvExtension α β σ) (env : Environment) (b : β) : Environment :=
ext.toEnvExtension.modifyState env $ fun s =>
  let state   := ext.addEntryFn s.state b;
  { s with state := state }

def getState {α β σ : Type} (ext : PersistentEnvExtension α β σ) (env : Environment) : σ :=
(ext.toEnvExtension.getState env).state

def setState {α β σ : Type} (ext : PersistentEnvExtension α β σ) (env : Environment) (s : σ) : Environment :=
ext.toEnvExtension.modifyState env $ fun ps => { ps with  state := s }

def modifyState {α β σ : Type} (ext : PersistentEnvExtension α β σ) (env : Environment) (f : σ → σ) : Environment :=
ext.toEnvExtension.modifyState env $ fun ps => { ps with state := f (ps.state) }

end PersistentEnvExtension

private def mkPersistentEnvExtensionsRef : IO (IO.Ref (Array (PersistentEnvExtension EnvExtensionEntry EnvExtensionEntry EnvExtensionState))) :=
IO.mkRef #[]

@[init mkPersistentEnvExtensionsRef]
private constant persistentEnvExtensionsRef : IO.Ref (Array (PersistentEnvExtension EnvExtensionEntry EnvExtensionEntry EnvExtensionState)) := arbitrary _

structure PersistentEnvExtensionDescr (α β σ : Type) :=
(name            : Name)
(mkInitial       : IO σ)
(addImportedFn   : Environment → Array (Array α) → IO σ)
(addEntryFn      : σ → β → σ)
(exportEntriesFn : σ → Array α)
(statsFn         : σ → Format := fun _ => Format.nil)

unsafe def registerPersistentEnvExtensionUnsafe {α β σ : Type} [Inhabited σ] (descr : PersistentEnvExtensionDescr α β σ) : IO (PersistentEnvExtension α β σ) := do
pExts ← persistentEnvExtensionsRef.get;
when (pExts.any (fun ext => ext.name == descr.name)) $ throw (IO.userError ("invalid environment extension, '" ++ toString descr.name ++ "' has already been used"));
ext ← registerEnvExtension $ do {
  initial ← descr.mkInitial;
  let s : PersistentEnvExtensionState α σ := {
    importedEntries := #[],
    state           := initial
  };
  pure s
};
let pExt : PersistentEnvExtension α β σ := {
  toEnvExtension  := ext,
  name            := descr.name,
  addImportedFn   := descr.addImportedFn,
  addEntryFn      := descr.addEntryFn,
  exportEntriesFn := descr.exportEntriesFn,
  statsFn         := descr.statsFn
};
persistentEnvExtensionsRef.modify $ fun pExts => pExts.push (unsafeCast pExt);
pure pExt

@[implementedBy registerPersistentEnvExtensionUnsafe]
constant registerPersistentEnvExtension {α β σ : Type} [Inhabited σ] (descr : PersistentEnvExtensionDescr α β σ) : IO (PersistentEnvExtension α β σ) := arbitrary _

/- Simple PersistentEnvExtension that implements exportEntriesFn using a list of entries. -/

def SimplePersistentEnvExtension (α σ : Type) := PersistentEnvExtension α α (List α × σ)

@[specialize] def mkStateFromImportedEntries {α σ : Type} (addEntryFn : σ → α → σ) (initState : σ) (as : Array (Array α)) : σ :=
as.foldl (fun r es => es.foldl (fun r e => addEntryFn r e) r) initState

structure SimplePersistentEnvExtensionDescr (α σ : Type) :=
(name          : Name)
(addEntryFn    : σ → α → σ)
(addImportedFn : Array (Array α) → σ)
(toArrayFn     : List α → Array α := fun es => es.toArray)

def registerSimplePersistentEnvExtension {α σ : Type} [Inhabited σ] (descr : SimplePersistentEnvExtensionDescr α σ) : IO (SimplePersistentEnvExtension α σ) :=
registerPersistentEnvExtension {
  name            := descr.name,
  mkInitial       := pure ([], descr.addImportedFn #[]),
  addImportedFn   := fun _ as => pure ([], descr.addImportedFn as),
  addEntryFn      := fun s e => match s with
    | (entries, s) => (e::entries, descr.addEntryFn s e),
  exportEntriesFn := fun s => descr.toArrayFn s.1.reverse,
  statsFn := fun s => format "number of local entries: " ++ format s.1.length
}

namespace SimplePersistentEnvExtension

instance {α σ : Type} [Inhabited σ] : Inhabited (SimplePersistentEnvExtension α σ) :=
inferInstanceAs (Inhabited (PersistentEnvExtension α α (List α × σ)))

def getEntries {α σ : Type} (ext : SimplePersistentEnvExtension α σ) (env : Environment) : List α :=
(PersistentEnvExtension.getState ext env).1

def getState {α σ : Type} (ext : SimplePersistentEnvExtension α σ) (env : Environment) : σ :=
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
  addImportedFn := fun as => {},
  addEntryFn    := fun s n => s.insert n,
  toArrayFn     := fun es => es.toArray.qsort Name.quickLt
}

namespace TagDeclarationExtension

instance : Inhabited TagDeclarationExtension :=
inferInstanceAs (Inhabited (SimplePersistentEnvExtension Name NameSet))

def tag (ext : TagDeclarationExtension) (env : Environment) (n : Name) : Environment :=
ext.addEntry env n

def isTagged (ext : TagDeclarationExtension) (env : Environment) (n : Name) : Bool :=
match env.getModuleIdxFor? n with
| some modIdx => (ext.getModuleEntries env modIdx).binSearchContains n Name.quickLt
| none        => (ext.getState env).contains n

end TagDeclarationExtension

/- API for creating extensions in C++.
   This API will eventually be deleted. -/
def CPPExtensionState := NonScalar

instance CPPExtensionState.inhabited : Inhabited CPPExtensionState := inferInstanceAs (Inhabited NonScalar)

section
/- It is not safe to use "extract closed term" optimization in the following code because of `unsafeIO`.
   If `compiler.extract_closed` is set to true, then the compiler will cache the result of
   `exts ← envExtensionsRef.get` during initialization which is incorrect. -/
set_option compiler.extract_closed false
@[export lean_register_extension]
unsafe def registerCPPExtension (initial : CPPExtensionState) : Option Nat :=
(unsafeIO (do ext ← registerEnvExtension (pure initial); pure ext.idx)).toOption

@[export lean_set_extension]
unsafe def setCPPExtensionState (env : Environment) (idx : Nat) (s : CPPExtensionState) : Option Environment :=
(unsafeIO (do exts ← envExtensionsRef.get; pure $ (exts.get! idx).setState env s)).toOption

@[export lean_get_extension]
unsafe def getCPPExtensionState (env : Environment) (idx : Nat) : Option CPPExtensionState :=
(unsafeIO (do exts ← envExtensionsRef.get; pure $ (exts.get! idx).getState env)).toOption
end

/- Legacy support for Modification objects -/

/- Opaque modification object. It is essentially a C `void *`.
   In Lean 3, a .olean file is essentially a collection of modification objects.
   This type represents the modification objects implemented in C++.
   We will eventually delete this type as soon as we port the remaining Lean 3
   legacy code.

   TODO: mark opaque -/
def Modification := NonScalar

instance Modification.inhabited : Inhabited Modification := inferInstanceAs (Inhabited NonScalar)

def regModListExtension : IO (EnvExtension (List Modification)) :=
registerEnvExtension (pure [])

@[init regModListExtension]
constant modListExtension : EnvExtension (List Modification) := arbitrary _

/- The C++ code uses this function to store the given modification object into the environment. -/
@[export lean_environment_add_modification]
def addModification (env : Environment) (mod : Modification) : Environment :=
modListExtension.modifyState env $ fun mods => mod :: mods

/- mkModuleData invokes this function to convert a list of modification objects into
   a serialized byte array. -/
@[extern 2 "lean_serialize_modifications"]
constant serializeModifications : List Modification → IO ByteArray := arbitrary _

@[extern 3 "lean_perform_serialized_modifications"]
constant performModifications : Environment → ByteArray → IO Environment := arbitrary _

/- Content of a .olean file.
   We use `compact.cpp` to generate the image of this object in disk. -/
structure ModuleData :=
(imports    : Array Import)
(constants  : Array ConstantInfo)
(entries    : Array (Name × Array EnvExtensionEntry))
(serialized : ByteArray) -- Legacy support: serialized modification objects

instance ModuleData.inhabited : Inhabited ModuleData :=
⟨{imports := arbitrary _, constants := arbitrary _, entries := arbitrary _, serialized := arbitrary _}⟩

@[extern 3 "lean_save_module_data"]
constant saveModuleData (fname : @& String) (m : ModuleData) : IO Unit := arbitrary _
@[extern 2 "lean_read_module_data"]
constant readModuleData (fname : @& String) : IO (ModuleData × CompactedRegion) := arbitrary _

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
pExts ← persistentEnvExtensionsRef.get;
let entries : Array (Name × Array EnvExtensionEntry) := pExts.size.fold
  (fun i result =>
    let state  := (pExts.get! i).getState env;
    let exportEntriesFn := (pExts.get! i).exportEntriesFn;
    let extName    := (pExts.get! i).name;
    result.push (extName, exportEntriesFn state))
  #[];
bytes ← serializeModifications (modListExtension.getState env);
pure {
  imports    := env.header.imports,
  constants  := env.constants.foldStage2 (fun cs _ c => cs.push c) #[],
  entries    := entries,
  serialized := bytes
}

@[export lean_write_module]
def writeModule (env : Environment) (fname : String) : IO Unit := do
modData ← mkModuleData env; saveModuleData fname modData

partial def importModulesAux : List Import → (NameSet × Array ModuleData × Array CompactedRegion) → IO (NameSet × Array ModuleData × Array CompactedRegion)
| [],    r         => pure r
| i::is, (s, mods, regions) =>
  if i.runtimeOnly || s.contains i.module then
    importModulesAux is (s, mods, regions)
  else do
    let s := s.insert i.module;
    mFile ← findOLean i.module;
    unlessM (IO.fileExists mFile) $
      throw $ IO.userError $ "object file '" ++ mFile ++ "' of module " ++ toString i.module ++ " does not exist";
    (mod, region) ← readModuleData mFile;
    (s, mods, regions) ← importModulesAux mod.imports.toList (s, mods, regions);
    let mods := mods.push mod;
    let regions := regions.push region;
    importModulesAux is (s, mods, regions)

private partial def getEntriesFor (mod : ModuleData) (extId : Name) : Nat → Array EnvExtensionState
| i =>
  if i < mod.entries.size then
    let curr := mod.entries.get! i;
    if curr.1 == extId then curr.2 else getEntriesFor (i+1)
  else
    #[]

private def setImportedEntries (env : Environment) (mods : Array ModuleData) : IO Environment := do
pExtDescrs ← persistentEnvExtensionsRef.get;
pure $ mods.iterate env $ fun _ mod env =>
  pExtDescrs.iterate env $ fun _ extDescr env =>
    let entries := getEntriesFor mod extDescr.name 0;
    extDescr.toEnvExtension.modifyState env $ fun s =>
      { s with importedEntries := s.importedEntries.push entries }

private def finalizePersistentExtensions (env : Environment) : IO Environment := do
pExtDescrs ← persistentEnvExtensionsRef.get;
pExtDescrs.iterateM env $ fun _ extDescr env => do
  let s := extDescr.toEnvExtension.getState env;
  newState ← extDescr.addImportedFn env s.importedEntries;
  pure $ extDescr.toEnvExtension.setState env { s with state := newState }

@[export lean_import_modules]
def importModules (imports : List Import) (trustLevel : UInt32 := 0) : IO Environment := do
(moduleNames, mods, regions) ← importModulesAux imports ({}, #[], #[]);
let const2ModIdx := mods.iterate {} $ fun (modIdx) (mod : ModuleData) (m : HashMap Name ModuleIdx) =>
  mod.constants.iterate m $ fun _ cinfo m =>
    m.insert cinfo.name modIdx.val;
constants ← mods.iterateM SMap.empty $ fun _ (mod : ModuleData) (cs : ConstMap) =>
  mod.constants.iterateM cs $ fun _ cinfo cs => do {
    when (cs.contains cinfo.name) $ throw (IO.userError ("import failed, environment already contains '" ++ toString cinfo.name ++ "'"));
    pure $ cs.insert cinfo.name cinfo
  };
let constants   := constants.switch;
exts ← mkInitialExtensionStates;
let env : Environment := {
  const2ModIdx := const2ModIdx,
  constants    := constants,
  extensions   := exts,
  header       := {
    quotInit     := !imports.isEmpty, -- We assume `core.lean` initializes quotient module
    trustLevel   := trustLevel,
    imports      := imports.toArray,
    regions      := regions,
    moduleNames  := moduleNames
  }
};
env ← setImportedEntries env mods;
env ← finalizePersistentExtensions env;
env ← mods.iterateM env $ fun _ mod env => performModifications env mod.serialized;
pure env

/--
  Create environment object from imports and free compacted regions after calling `act`. No live references to the
  environment object or imported objects may exist after `act` finishes. -/
unsafe def withImportModules {α : Type} (imports : List Import) (trustLevel : UInt32 := 0) (x : Environment → IO α) : IO α := do
env ← importModules imports trustLevel;
finally (x env) env.freeRegions

def regNamespacesExtension : IO (SimplePersistentEnvExtension Name NameSet) :=
registerSimplePersistentEnvExtension {
  name            := `namespaces,
  addImportedFn   := fun as => mkStateFromImportedEntries NameSet.insert {} as,
  addEntryFn      := fun s n => s.insert n
}

@[init regNamespacesExtension]
constant namespacesExt : SimplePersistentEnvExtension Name NameSet := arbitrary _

def registerNamespace (env : Environment) (n : Name) : Environment :=
if (namespacesExt.getState env).contains n then env else namespacesExt.addEntry env n

def isNamespace (env : Environment) (n : Name) : Bool :=
(namespacesExt.getState env).contains n

def getNamespaceSet (env : Environment) : NameSet :=
namespacesExt.getState env

namespace Environment

private def isNamespaceName : Name → Bool
| Name.str Name.anonymous _ _ => true
| Name.str p _ _              => isNamespaceName p
| _                           => false

private def registerNamePrefixes : Environment → Name → Environment
| env, Name.str p _ _ => if isNamespaceName p then registerNamePrefixes (registerNamespace env p) p else env
| env, _              => env

@[export lean_environment_add]
def add (env : Environment) (cinfo : ConstantInfo) : Environment :=
let env := registerNamePrefixes env cinfo.name;
env.addAux cinfo

@[export lean_display_stats]
def displayStats (env : Environment) : IO Unit := do
pExtDescrs ← persistentEnvExtensionsRef.get;
let numModules := ((pExtDescrs.get! 0).toEnvExtension.getState env).importedEntries.size;
IO.println ("direct imports:                        " ++ toString env.header.imports);
IO.println ("number of imported modules:            " ++ toString numModules);
IO.println ("number of consts:                      " ++ toString env.constants.size);
IO.println ("number of imported consts:             " ++ toString env.constants.stageSizes.1);
IO.println ("number of local consts:                " ++ toString env.constants.stageSizes.2);
IO.println ("number of buckets for imported consts: " ++ toString env.constants.numBuckets);
IO.println ("trust level:                           " ++ toString env.header.trustLevel);
IO.println ("number of extensions:                  " ++ toString env.extensions.size);
pExtDescrs.forM $ fun extDescr => do {
  IO.println ("extension '" ++ toString extDescr.name ++ "'");
  let s := extDescr.toEnvExtension.getState env;
  let fmt := extDescr.statsFn s.state;
  unless fmt.isNil (IO.println ("  " ++ toString (Format.nest 2 (extDescr.statsFn s.state))));
  IO.println ("  number of imported entries: " ++ toString (s.importedEntries.foldl (fun sum es => sum + es.size) 0));
  pure ()
};
pure ()

@[extern "lean_eval_const"]
unsafe constant evalConst (α) (env : @& Environment) (constName : @& Name) : Except String α := arbitrary _

private def throwUnexpectedType {α} (typeName : Name) (constName : Name) : ExceptT String Id α :=
throw ("unexpected type at '" ++ toString constName ++ "', `" ++ toString typeName ++ "` expected")

/-- Like `evalConst`, but first check that `constName` indeed is a declaration of type `typeName`.
    This function is still unsafe because it cannot guarantee that `typeName` is in fact the name of the type `α`. -/
unsafe def evalConstCheck (α) (env : Environment) (typeName : Name) (constName : Name) : ExceptT String Id α :=
match env.find? constName with
| none      => throw ("unknow constant '" ++ toString constName ++ "'")
| some info =>
  match info.type with
  | Expr.const c _ _ =>
    if c != typeName then throwUnexpectedType typeName constName
    else env.evalConst α constName
  | _ => throwUnexpectedType typeName constName

def hasUnsafe (env : Environment) (e : Expr) : Bool :=
let c? := e.find? $ fun e => match e with
  | Expr.const c _ _ =>
    match env.find? c with
    | some cinfo => cinfo.isUnsafe
    | none       => false
  | _ => false;
c?.isSome

end Environment

/- Helper functions for accessing environment -/

@[inline]
def matchConst {α : Type} (env : Environment) (e : Expr) (failK : Unit → α) (k : ConstantInfo → List Level → α) : α :=
match e with
| Expr.const n lvls _ =>
  match env.find? n with
  | some cinfo => k cinfo lvls
  | _          => failK ()
| _ => failK ()

namespace Kernel
/- Kernel API -/

/--
  Kernel isDefEq predicate. We use it mainly for debugging purposes.
  Recall that the Kernel type checker does not support metavariables.
  When implementing automation, consider using the `MetaM` methods. -/
@[extern "lean_kernel_is_def_eq"]
constant isDefEq (env : Environment) (lctx : LocalContext) (a b : Expr) : Bool := arbitrary _

/--
  Kernel WHNF function. We use it mainly for debugging purposes.
  Recall that the Kernel type checker does not support metavariables.
  When implementing automation, consider using the `MetaM` methods. -/
@[extern "lean_kernel_whnf"]
constant whnf (env : Environment) (lctx : LocalContext) (a : Expr) : Expr := arbitrary _

end Kernel

end Lean
