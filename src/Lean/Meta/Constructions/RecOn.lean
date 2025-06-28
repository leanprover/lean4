/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Joachim Breitner
-/
prelude
import Lean.Meta.InferType
import Lean.AuxRecursor
import Lean.AddDecl
import Lean.Meta.CompletionName

open Lean Meta

def mkRecOn (n : Name) : MetaM Unit := do
  let .recInfo recInfo ← getConstInfo (mkRecName n)
    | throwError "{mkRecName n} not a recinfo"
  let decl ← forallTelescope recInfo.type fun xs t => do
    let e := .const recInfo.name (recInfo.levelParams.map (.param ·))
    let e := mkAppN e xs
    -- We reorder the parameters
    -- before: As Cs minor_premises indices major-premise
    -- fow:    As Cs indices major-premise minor-premises
    let AC_size := xs.size - recInfo.numMinors - recInfo.numIndices - 1
    let vs :=
      xs[:AC_size] ++
      xs[AC_size + recInfo.numMinors:AC_size + recInfo.numMinors + 1 + recInfo.numIndices] ++
      xs[AC_size:AC_size + recInfo.numMinors]
    let type ← mkForallFVars vs t
    let value ← mkLambdaFVars vs e
    mkDefinitionValInferrringUnsafe (mkRecOnName n) recInfo.levelParams type value .abbrev

  addDecl (.defnDecl decl)
  setReducibleAttribute decl.name
  modifyEnv fun env => markAuxRecursor env decl.name
  modifyEnv fun env => addProtected env decl.name
