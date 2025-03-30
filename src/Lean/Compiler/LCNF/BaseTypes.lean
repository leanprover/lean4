/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Compiler.LCNF.CompilerM
import Lean.Compiler.LCNF.Types

namespace Lean.Compiler.LCNF

/--
State for the environment extension used to save the LCNF base phase type for declarations
that do not have code associated with them.
Example: constructors, inductive types, foreign functions.
-/
structure BaseTypeExtState where
  /-- The LCNF type for the `base` phase. -/
  base : PHashMap Name Expr := {}
  deriving Inhabited

builtin_initialize baseTypeExt : EnvExtension BaseTypeExtState ←
  registerEnvExtension (pure {}) (asyncMode := .sync)  -- compilation is non-parallel anyway

def getOtherDeclBaseType (declName : Name) (us : List Level) : CoreM Expr := do
  let info ← getConstInfo declName
  let type ← match baseTypeExt.getState (← getEnv) |>.base.find? declName with
    | some type => pure type
    | none =>
      let type ← Meta.MetaM.run' <| toLCNFType info.type
      modifyEnv fun env => baseTypeExt.modifyState env fun s => { s with base := s.base.insert declName type }
      pure type
  return type.instantiateLevelParamsNoCache info.levelParams us

end Lean.Compiler.LCNF
