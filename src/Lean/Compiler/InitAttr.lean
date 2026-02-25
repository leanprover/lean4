/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.AddDecl
public import Lean.Elab.InfoTree.Main
import Init.Data.Range.Polymorphic.Stream
import Lean.Compiler.NameMangling
import Lean.Compiler.ModPkgExt

public section

namespace Lean

private def getIOTypeArg : Expr → Option Expr
  | Expr.app (Expr.const `IO _) arg => some arg
  | _                               => none

private def isUnitType : Expr → Bool
  | Expr.const `Unit _ => true
  | _                  => false

private def isIOUnit (type : Expr) : Bool :=
  match getIOTypeArg type with
  | some type => isUnitType type
  | _ => false

@[extern "lean_run_mod_init_core"]
private unsafe opaque runModInitCore (sym : @& String) : IO Bool

/--
Run the initializer of the given module (without `builtin_initialize` commands).
Return `false` if the initializer is not available as native code.
Initializers do not have corresponding Lean definitions, so they cannot be interpreted in this case.
-/
@[inline] private unsafe def runModInit (mod : Name) (pkg? : Option String) : IO Bool :=
  runModInitCore (mkModuleInitializationFunctionName mod pkg?)

/-- Run the initializer for `decl` and store its value for global access. Should only be used while importing. -/
@[extern "lean_run_init"]
unsafe opaque runInit (env : @& Environment) (opts : @& Options) (decl initDecl : @& Name) : IO Unit

/-- Set of modules for which we have already run the module initializer in the interpreter. -/
builtin_initialize interpretedModInits : IO.Ref NameSet ← IO.mkRef {}

unsafe def registerInitAttrUnsafe (attrName : Name) (runAfterImport : Bool) (ref : Name) : IO (ParametricAttribute Name) :=
  registerParametricAttribute {
    ref := ref
    name := attrName
    descr := "initialization procedure for global references"
    -- We want to run `[init]` in declaration order
    preserveOrder := true
    getParam := fun declName stx => do
      let decl ← getConstInfo declName
      match (← Attribute.Builtin.getIdent? stx) with
      | some initFnName =>
        let initFnName ← Elab.realizeGlobalConstNoOverloadWithInfo initFnName
        let initDecl ← getConstInfo initFnName
        match getIOTypeArg initDecl.type with
        | none => throwError "initialization function `{initFnName}` must have type of the form `IO <type>`"
        | some initTypeArg =>
          if decl.type == initTypeArg then pure initFnName
          else throwError "initialization function `{initFnName}` type mismatch"
      | none =>
        if isIOUnit decl.type then pure Name.anonymous
        else throwError "initialization function must have type `IO Unit`"
    -- Save `meta initialize` in .olean; `initialize`s of any kind will be stored in .ir by
    -- `exportIREntries` analogously to `Lean.IR.declMapExt` so we can run them when meta-imported,
    -- even without the .olean file.
    filterExport := fun env declName _ =>
      -- TODO: The interpreter currently depends on `[builtin_init]` to be exported for
      -- `prefer_native` handling but this is incorrect with private imports anyway and should be
      -- replaced by consulting a builtin list.
      !runAfterImport || isMarkedMeta env declName
  }

@[implemented_by registerInitAttrUnsafe]
private opaque registerInitAttrInner (attrName : Name) (runAfterImport : Bool) (ref : Name) : IO (ParametricAttribute Name)

@[inline]
def registerInitAttr (attrName : Name) (runAfterImport : Bool) (ref : Name := by exact decl_name%) : IO (ParametricAttribute Name) :=
  registerInitAttrInner attrName runAfterImport ref

/--
Registers an initialization procedure. Initialization procedures are run in files that import the
file they are defined in.

This attribute comes in two kinds: Without arguments, the tagged declaration should have type
`IO Unit` and are simply run during initialization. With a declaration name as a argument, the
tagged declaration should be an opaque constant and the provided declaration name an action in `IO`
that returns a value of the type of the tagged declaration. Such initialization procedures store
the resulting value and make it accessible through the tagged declaration.

The `initialize` command should usually be preferred over using this attribute directly.
-/
@[builtin_doc]
builtin_initialize regularInitAttr : ParametricAttribute Name ← registerInitAttr `init true

/--
Registers a builtin initialization procedure.

This attribute is used internally to define builtin initialization procedures for bootstrapping and
should not be used otherwise.
-/
@[builtin_doc]
builtin_initialize builtinInitAttr : ParametricAttribute Name ← registerInitAttr `builtin_init false

def getInitFnNameForCore? (env : Environment) (attr : ParametricAttribute Name) (fn : Name) : Option Name :=
  match attr.getParam? env fn with
  | some Name.anonymous => none
  | some n              => some n
  | _                   => none

def getBuiltinInitFnNameFor? (env : Environment) (fn : Name) : Option Name :=
  getInitFnNameForCore? env builtinInitAttr fn

@[export lean_get_regular_init_fn_name_for]
def getRegularInitFnNameFor? (env : Environment) (fn : Name) : Option Name :=
  getInitFnNameForCore? env regularInitAttr fn

@[export lean_get_init_fn_name_for]
def getInitFnNameFor? (env : Environment) (fn : Name) : Option Name :=
  getBuiltinInitFnNameFor? env fn <|> getRegularInitFnNameFor? env fn

def isIOUnitInitFnCore (env : Environment) (attr : ParametricAttribute Name) (fn : Name) : Bool :=
  match attr.getParam? env fn with
  | some Name.anonymous => true
  | _ => false

def isIOUnitRegularInitFn (env : Environment) (fn : Name) : Bool :=
  isIOUnitInitFnCore env regularInitAttr fn

def isIOUnitBuiltinInitFn (env : Environment) (fn : Name) : Bool :=
  isIOUnitInitFnCore env builtinInitAttr fn

def isIOUnitInitFn (env : Environment) (fn : Name) : Bool :=
  isIOUnitBuiltinInitFn env fn || isIOUnitRegularInitFn env fn

def hasInitAttr (env : Environment) (fn : Name) : Bool :=
  (getInitFnNameFor? env fn).isSome

def setBuiltinInitAttr (env : Environment) (declName : Name) (initFnName : Name := Name.anonymous) : Except String Environment :=
  builtinInitAttr.setParam env declName initFnName

def declareBuiltin (forDecl : Name) (value : Expr) : CoreM Unit :=
  -- can always be private, not referenced directly except through emitted C code
  withoutExporting do
  -- TODO: needs an update-stage0 + prefer_native=true for breaking symbol name
  withExporting do
    let name ← mkAuxDeclName (kind := `_regBuiltin ++ forDecl)
    let type := mkApp (mkConst `IO) (mkConst `Unit)
    let decl := Declaration.defnDecl { name, levelParams := [], type, value, hints := ReducibilityHints.opaque,
                                       safety := DefinitionSafety.safe }
    addAndCompile decl
    IO.ofExcept (setBuiltinInitAttr (← getEnv) name) >>= setEnv

@[export lean_run_init_attrs]
private unsafe def runInitAttrs (env : Environment) (opts : Options) : IO Unit := do
  if (← isInitializerExecutionEnabled) then
    -- **Note**: `ModuleIdx` is not an abbreviation, and we don't have instances for it.
    -- Thus, we use `(modIdx : Nat)`
    for mod in env.header.moduleNames, (modIdx : Nat) in 0...* do
      -- any native Lean code reachable by the interpreter (i.e. from shared
      -- libraries with their corresponding module in the Environment) must
      -- first be initialized
      let pkg? := env.getModulePackageByIdx? modIdx
      if (← runModInit mod pkg?) then
        continue
      -- As `[init]` decls can have global side effects, ensure we run them at most once,
      -- just like the compiled code does.
      if (← interpretedModInits.get).contains mod then
        continue
      interpretedModInits.modify (·.insert mod)
      let modEntries := regularInitAttr.ext.getModuleEntries env modIdx
      -- `getModuleIREntries` is identical to `getModuleEntries` if we loaded only one of
      -- .olean (from `meta initialize`)/.ir (`initialize` via transitive `meta import`)
      -- so deduplicate (these lists should be very short).
      -- If we have both, we should not need to worry about their relative ordering as `meta` and
      -- non-`meta` initialize should not have interdependencies.
      let modEntries := modEntries ++ (regularInitAttr.ext.getModuleIREntries env modIdx).filter (!modEntries.contains ·)
      for (decl, initDecl) in modEntries do
        -- Skip initializers we do not have IR for; they should not be reachable by interpretation.
        if !Elab.inServer.get opts && getIRPhases env decl == .runtime then
          continue
        if initDecl.isAnonymous then
          -- Don't check `meta` again as it would not respect `Elab.inServer`
          let initFn ← IO.ofExcept <| env.evalConst (checkMeta := false) (IO Unit) opts decl
          initFn
        else
          runInit env opts decl initDecl

end Lean
