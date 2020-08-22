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

def mkInitAttr : IO (ParametricAttribute Name) :=
registerParametricAttribute `init "initialization procedure for global references" $ fun declName stx => do
  decl ← getConstInfo declName;
  match attrParamSyntaxToIdentifier stx with
  | some initFnName => do
    initDecl ← getConstInfo initFnName;
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

@[init mkInitAttr]
constant initAttr : ParametricAttribute Name := arbitrary _

def isIOUnitInitFn (env : Environment) (fn : Name) : Bool :=
match initAttr.getParam env fn with
| some Name.anonymous => true
| _ => false

@[export lean_get_init_fn_name_for]
def getInitFnNameFor (env : Environment) (fn : Name) : Option Name :=
match initAttr.getParam env fn with
| some Name.anonymous => none
| some n => some n
| _ => none

def hasInitAttr (env : Environment) (fn : Name) : Bool :=
(getInitFnNameFor env fn).isSome

def setInitAttr (env : Environment) (declName : Name) (initFnName : Name := Name.anonymous) : Except String Environment :=
initAttr.setParam env declName initFnName

end Lean
