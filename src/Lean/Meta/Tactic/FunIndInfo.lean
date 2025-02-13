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
This module defines the data structure and environment extension to remember how to map the function's arguments to the induction principle's argument.

TODO: What if two independent modules realize the constant?
-/

namespace Lean.Meta

inductive FunIndParamKind where
  | dropped
  | param
  | target
deriving BEq, Repr

structure FunIndInfo where
  funIndName : Name
  levelMask : Array Bool
  params : Array FunIndParamKind
deriving Inhabited, Repr

builtin_initialize funIndInfoExt : MapDeclarationExtension FunIndInfo ← mkMapDeclarationExtension

-- TODO: Use everywhere
def getFunInductName (declName : Name) : Name :=
  declName ++ `induct

-- TODO: Moved from try? use getFunIndInfo? there
def getFunInduct? (declName : Name) : CoreM (Option Name) := do
  let .defnInfo _ ← getConstInfo declName | return none
  try
    let result ← realizeGlobalConstNoOverloadCore (getFunInductName declName)
    return some result
  catch _ =>
    return none

def setFunIndInfo (funIndInfo : FunIndInfo) : CoreM Unit := do
  assert! !(funIndInfoExt.contains (← getEnv) funIndInfo.funIndName)
  modifyEnv fun env => funIndInfoExt.insert env funIndInfo.funIndName funIndInfo

def getFunIndInfoForInduct? (inductName : Name) : CoreM (Option FunIndInfo) := do
  return funIndInfoExt.find? (← getEnv) inductName

def getFunIndInfo? (funName : Name) : CoreM (Option FunIndInfo) := do
  let some inductName ← getFunInduct? funName  | return none
  getFunIndInfoForInduct? inductName

end Lean.Meta
