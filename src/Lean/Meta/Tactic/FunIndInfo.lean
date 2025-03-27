/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

prelude
import Lean.Meta.Basic
import Lean.ScopedEnvExtension
import Lean.ReservedNameAction

/-!
This module defines the data structure and environment extension to remember how to map the
function's arguments to the functional induction principle's arguments.
Also used for functional cases.
-/

namespace Lean.Meta

inductive FunIndParamKind where
  | dropped
  | param
  | target
deriving BEq, Repr, Inhabited

/--
A `FunIndInfo` indicates how a function's arguments map to the arguments of the functional induction
(resp. cases) theorem.

The size of `params` also indicates the arity of the function.
-/
structure FunIndInfo where
  funIndName : Name
  /--
  `true` means that the corresponding level parameter of the function is also a level param
  of the induction principle.
  -/
  levelMask : Array Bool
  params : Array FunIndParamKind
deriving Inhabited, Repr

builtin_initialize funIndInfoExt : MapDeclarationExtension FunIndInfo ← mkMapDeclarationExtension

def getFunInductName (declName : Name) : Name :=
  declName ++ `induct

def getFunCasesName (declName : Name) : Name :=
  declName ++ `fun_cases

def getMutualInductName (declName : Name) : Name :=
  declName ++ `mutual_induct

def getFunInduct? (cases : Bool) (declName : Name) : CoreM (Option Name) := do
  let .defnInfo _ ← getConstInfo declName | return none
  try
    let thmName := if cases then
      getFunCasesName declName
    else
      getFunInductName declName
    let result ← realizeGlobalConstNoOverloadCore thmName
    return some result
  catch _ =>
    return none

def setFunIndInfo (funIndInfo : FunIndInfo) : CoreM Unit := do
  assert! !(funIndInfoExt.contains (← getEnv) funIndInfo.funIndName)
  modifyEnv fun env => funIndInfoExt.insert env funIndInfo.funIndName funIndInfo

def getFunIndInfoForInduct?  (inductName : Name) : CoreM (Option FunIndInfo) := do
  return funIndInfoExt.find? (← getEnv) inductName

def getFunIndInfo? (cases : Bool) (funName : Name) : CoreM (Option FunIndInfo) := do
  let some inductName ← getFunInduct? cases funName | return none
  getFunIndInfoForInduct? inductName

end Lean.Meta
