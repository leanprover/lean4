/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNF.CompilerM
import Lean.Compiler.LCNF.Types

namespace Lean.Compiler.LCNF

/--
State for the environment extension used to save the type of declarations
that do not have code associated with them.
Example: constructors, inductive types, foreign functions.
-/
structure OtherTypeExtState where
  /-- The LCNF type for the `base` phase. -/
  base : PHashMap Name Expr := {}
  /-- The LCNF type for the `mono` phase. -/
  mono : PHashMap Name Expr := {}
  deriving Inhabited

builtin_initialize otherTypeExt : EnvExtension OtherTypeExtState ←
  registerEnvExtension (pure {})

def getOtherDeclBaseType (declName : Name) (us : List Level) : CoreM Expr := do
  let info ← getConstInfo declName
  let type ← match otherTypeExt.getState (← getEnv) |>.base.find? declName with
    | some type => pure type
    | none =>
      let type ← Meta.MetaM.run' <| toLCNFType info.type
      modifyEnv fun env => otherTypeExt.modifyState env fun s => { s with base := s.base.insert declName type }
      pure type
  return type.instantiateLevelParams info.levelParams us

/--
Return the LCNF type for constructors, inductive types, and foreign functions.
-/
def getOtherDeclType (declName : Name) (us : List Level := []) : CompilerM Expr := do
  match (← getPhase) with
  | .base => getOtherDeclBaseType declName us
  | _ => unreachable! -- TODO

end Lean.Compiler.LCNF
