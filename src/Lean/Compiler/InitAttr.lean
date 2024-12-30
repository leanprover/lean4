/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.AddDecl
import Lean.MonadEnv
import Lean.Elab.InfoTree.Main

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

/--
  Run the initializer of the given module (without `builtin_initialize` commands).
  Return `false` if the initializer is not available as native code.
  Initializers do not have corresponding Lean definitions, so they cannot be interpreted in this case. -/
@[extern "lean_run_mod_init"]
unsafe opaque runModInit (mod : Name) : IO Bool

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
    getParam := fun declName stx => do
      let decl ← getConstInfo declName
      match (← Attribute.Builtin.getIdent? stx) with
      | some initFnName =>
        let initFnName ← Elab.realizeGlobalConstNoOverloadWithInfo initFnName
        let initDecl ← getConstInfo initFnName
        match getIOTypeArg initDecl.type with
        | none => throwError "initialization function '{initFnName}' must have type of the form `IO <type>`"
        | some initTypeArg =>
          if decl.type == initTypeArg then pure initFnName
          else throwError "initialization function '{initFnName}' type mismatch"
      | none =>
        if isIOUnit decl.type then pure Name.anonymous
        else throwError "initialization function must have type `IO Unit`"
    afterImport := fun entries => do
      let ctx ← read
      if runAfterImport && (← isInitializerExecutionEnabled) then
        for mod in ctx.env.header.moduleNames,
            modData in ctx.env.header.moduleData,
            modEntries in entries do
          -- any native Lean code reachable by the interpreter (i.e. from shared
          -- libraries with their corresponding module in the Environment) must
          -- first be initialized
          if (← runModInit mod) then
            continue
          -- If no native code for the module is available, run `[init]` decls manually.
          -- All other constants (nullary functions) are lazily initialized by the interpreter.
          if modEntries.isEmpty then
            -- If there are no `[init]` decls, don't bother walking through all module decls.
            -- We do this after trying `runModInit` as that one may also efficiently initialize
            -- nullary functions.
            continue
          -- As `[init]` decls can have global side effects, ensure we run them at most once,
          -- just like the compiled code does.
          if (← interpretedModInits.get).contains mod then
            continue
          interpretedModInits.modify (·.insert mod)
          for c in modData.constNames do
            -- make sure to run initializers in declaration order, not extension state order, to respect dependencies
            if let some (decl, initDecl) := modEntries.binSearch (c, default) (Name.quickLt ·.1 ·.1) then
              if initDecl.isAnonymous then
                let initFn ← IO.ofExcept <| ctx.env.evalConst (IO Unit) ctx.opts decl
                initFn
              else
                runInit ctx.env ctx.opts decl initDecl
  }

@[implemented_by registerInitAttrUnsafe]
private opaque registerInitAttrInner (attrName : Name) (runAfterImport : Bool) (ref : Name) : IO (ParametricAttribute Name)

@[inline]
def registerInitAttr (attrName : Name) (runAfterImport : Bool) (ref : Name := by exact decl_name%) : IO (ParametricAttribute Name) :=
  registerInitAttrInner attrName runAfterImport ref

builtin_initialize regularInitAttr : ParametricAttribute Name ← registerInitAttr `init true
builtin_initialize builtinInitAttr : ParametricAttribute Name ← registerInitAttr `builtin_init false

def getInitFnNameForCore? (env : Environment) (attr : ParametricAttribute Name) (fn : Name) : Option Name :=
  match attr.getParam? env fn with
  | some Name.anonymous => none
  | some n              => some n
  | _                   => none

@[export lean_get_builtin_init_fn_name_for]
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

@[export lean_is_io_unit_regular_init_fn]
def isIOUnitRegularInitFn (env : Environment) (fn : Name) : Bool :=
  isIOUnitInitFnCore env regularInitAttr fn

@[export lean_is_io_unit_builtin_init_fn]
def isIOUnitBuiltinInitFn (env : Environment) (fn : Name) : Bool :=
  isIOUnitInitFnCore env builtinInitAttr fn

def isIOUnitInitFn (env : Environment) (fn : Name) : Bool :=
  isIOUnitBuiltinInitFn env fn || isIOUnitRegularInitFn env fn

def hasInitAttr (env : Environment) (fn : Name) : Bool :=
  (getInitFnNameFor? env fn).isSome

def setBuiltinInitAttr (env : Environment) (declName : Name) (initFnName : Name := Name.anonymous) : Except String Environment :=
  builtinInitAttr.setParam env declName initFnName

def declareBuiltin (forDecl : Name) (value : Expr) : CoreM Unit := do
  let name ← mkAuxName (`_regBuiltin ++ forDecl) 1
  let type := mkApp (mkConst `IO) (mkConst `Unit)
  let decl := Declaration.defnDecl { name, levelParams := [], type, value, hints := ReducibilityHints.opaque,
                                     safety := DefinitionSafety.safe }
  try
    addAndCompile decl
  catch e => do
    -- TODO: pretty print error
    let msg ← e.toMessageData.toString
    throwError "failed to emit registration code for builtin '{forDecl}': {msg}"
  IO.ofExcept (setBuiltinInitAttr (← getEnv) name) >>= setEnv

end Lean
