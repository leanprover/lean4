/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Environment

namespace Lean

def casesOnSuffix       := "casesOn"
def recOnSuffix         := "recOn"
def brecOnSuffix        := "brecOn"
def binductionOnSuffix  := "binductionOn"
def belowSuffix         := "below"
def ibelowSuffix        := "ibelow"

def mkCasesOnName (indDeclName : Name) : Name := Name.mkStr indDeclName casesOnSuffix
def mkRecOnName (indDeclName : Name) : Name   := Name.mkStr indDeclName recOnSuffix
def mkBRecOnName (indDeclName : Name) : Name  := Name.mkStr indDeclName brecOnSuffix
def mkBInductionOnName (indDeclName : Name) : Name  := Name.mkStr indDeclName binductionOnSuffix
def mkBelowName (indDeclName : Name) : Name := Name.mkStr indDeclName belowSuffix
def mkIBelowName (indDeclName : Name) : Name := Name.mkStr indDeclName ibelowSuffix

builtin_initialize auxRecExt : TagDeclarationExtension ← mkTagDeclarationExtension

def markAuxRecursor (env : Environment) (declName : Name) : Environment :=
  auxRecExt.tag env declName

@[export lean_is_aux_recursor]
def isAuxRecursor (env : Environment) (declName : Name) : Bool :=
  auxRecExt.isTagged env declName
  -- TODO: use `markAuxRecursor` when they are defined
  -- An attribute is not a good solution since we don't want users to control what is tagged as an auxiliary recursor.
  || declName == ``Eq.ndrec
  || declName == ``Eq.ndrecOn

def isAuxRecursorWithSuffix (env : Environment) (declName : Name) (suffix : String) : Bool :=
  match declName with
  | .str _ s => (s == suffix || s.startsWith s!"{suffix}_") && isAuxRecursor env declName
  | _ => false

def isCasesOnRecursor (env : Environment) (declName : Name) : Bool :=
  isAuxRecursorWithSuffix env declName casesOnSuffix

def isRecOnRecursor (env : Environment) (declName : Name) : Bool :=
  isAuxRecursorWithSuffix env declName recOnSuffix

def isBRecOnRecursor (env : Environment) (declName : Name) : Bool :=
  isAuxRecursorWithSuffix env declName brecOnSuffix

builtin_initialize noConfusionExt : TagDeclarationExtension ← mkTagDeclarationExtension

def markNoConfusion (env : Environment) (n : Name) : Environment :=
  noConfusionExt.tag env n

@[export lean_is_no_confusion]
def isNoConfusion (env : Environment) (n : Name) : Bool :=
  noConfusionExt.isTagged env n

end Lean
