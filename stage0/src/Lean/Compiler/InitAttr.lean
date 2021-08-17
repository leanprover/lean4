/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Environment
import Lean.Attributes

namespace Lean

private def getIOTypeArg : Expr → Option Expr
  | Expr.app (Expr.const `IO _ _) arg _ => some arg
  | _                                   => none

private def isUnitType : Expr → Bool
  | Expr.const `Unit _ _ => true
  | _                    => false

private def isIOUnit (type : Expr) : Bool :=
  match getIOTypeArg type with
  | some type => isUnitType type
  | _ => false

/-- Run the initializer for `decl` and store its value for global access. Should only be used while importing. -/
@[extern "lean_run_init"]
unsafe constant runInit (env : @& Environment) (opts : @& Options) (decl initDecl : @& Name) : IO Unit

unsafe def registerInitAttrUnsafe (attrName : Name) (runAfterImport : Bool) : IO (ParametricAttribute Name) :=
  registerParametricAttribute {
    name := attrName,
    descr := "initialization procedure for global references",
    getParam := fun declName stx => do
      let decl ← getConstInfo declName
      match (← Attribute.Builtin.getIdent? stx) with
      | some initFnName =>
        let initFnName ← resolveGlobalConstNoOverload initFnName
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
        for modEntries in entries do
          for (decl, initDecl) in modEntries do
            if initDecl.isAnonymous then
              let initFn ← IO.ofExcept <| ctx.env.evalConst (IO Unit) ctx.opts decl
              initFn
            else
              runInit ctx.env ctx.opts decl initDecl
  }

@[implementedBy registerInitAttrUnsafe]
constant registerInitAttr (attrName : Name) (runAfterImport : Bool) : IO (ParametricAttribute Name)

builtin_initialize regularInitAttr : ParametricAttribute Name ← registerInitAttr `init true
builtin_initialize builtinInitAttr : ParametricAttribute Name ← registerInitAttr `builtinInit false

def getInitFnNameForCore? (env : Environment) (attr : ParametricAttribute Name) (fn : Name) : Option Name :=
  match attr.getParam env fn with
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
  match attr.getParam env fn with
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

end Lean
