#lang lean4
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

def registerInitAttr (attrName : Name) : IO (ParametricAttribute Name) :=
registerParametricAttribute attrName "initialization procedure for global references" fun declName stx => do
  let decl ← getConstInfo declName
  match attrParamSyntaxToIdentifier stx with
  | some initFnName =>
    let initFnName ← resolveGlobalConstNoOverload initFnName
    let initDecl ← getConstInfo initFnName
    match getIOTypeArg initDecl.type with
    | none => throwError ("initialization function '" ++ initFnName ++ "' must have type of the form `IO <type>`")
    | some initTypeArg =>
      if decl.type == initTypeArg then pure initFnName
      else throwError ("initialization function '" ++ initFnName ++ "' type mismatch")
  | _ => match stx with
    | Syntax.missing =>
      if isIOUnit decl.type then pure Name.anonymous
      else throwError "initialization function must have type `IO Unit`"
    | _ => throwError "unexpected kind of argument"

builtin_initialize regularInitAttr : ParametricAttribute Name ← registerInitAttr `init
builtin_initialize builtinInitAttr : ParametricAttribute Name ← registerInitAttr `builtinInit

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

-- Only used
def isIOUnitInitFn (env : Environment) (fn : Name) : Bool :=
let aux (attr : ParametricAttribute Name) : Bool :=
  match attr.getParam env fn with
  | some Name.anonymous => true
  | _ => false
aux builtinInitAttr || aux regularInitAttr

@[export lean_get_init_fn_name_for]
def getInitFnNameFor? (env : Environment) (fn : Name) : Option Name :=
getBuiltinInitFnNameFor? env fn <|> getRegularInitFnNameFor? env fn

def hasInitAttr (env : Environment) (fn : Name) : Bool :=
(getInitFnNameFor? env fn).isSome

def setBuiltinInitAttr (env : Environment) (declName : Name) (initFnName : Name := Name.anonymous) : Except String Environment :=
-- builtinInitAttr.setParam env declName initFnName -- TODO: use this one
regularInitAttr.setParam env declName initFnName

end Lean
