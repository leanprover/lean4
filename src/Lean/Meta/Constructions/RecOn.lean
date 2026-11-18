/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Joachim Breitner
-/
module

prelude
public import Lean.AddDecl
public import Lean.Meta.CompletionName
public import Lean.Meta.Constructions.CasesOn

public section

open Lean Meta

namespace Lean

/--
Defines `recOn` for `declName` to be its `casesOn`, or returns `none` if `casesOn` is not built from
projections or has not been built yet.

A type eligible for `mkCasesOnViaProjs?` is neither recursive nor indexed, so its `recOn` and
`casesOn` have the same type, and rebuilding the projections would just repeat the work.
-/
def mkRecOnViaCasesOn? (declName : Name) : MetaM (Option DefinitionVal) := do
  let casesOnName := mkCasesOnName declName
  unless (← getEnv).contains casesOnName do return none
  unless (← isCasesOnViaProjs declName) do return none
  let casesOnInfo ← getConstInfo casesOnName
  let value := .const casesOnName (casesOnInfo.levelParams.map (.param ·))
  return some (← mkDefinitionValInferringUnsafe (mkRecOnName declName) casesOnInfo.levelParams
    casesOnInfo.type value .abbrev)

def mkRecOn (n : Name) : MetaM Unit := do
  let .recInfo recInfo ← getConstInfo (mkRecName n)
    | throwError "{mkRecName n} not a recinfo"
  let decl ← match ← mkRecOnViaCasesOn? n with
   | some decl => pure decl
   | none => forallTelescope recInfo.type fun xs t => do
      let e := .const recInfo.name (recInfo.levelParams.map (.param ·))
      let e := mkAppN e xs
      -- We reorder the parameters
      -- before: As Cs minor_premises indices major-premise
      -- fow:    As Cs indices major-premise minor-premises
      let AC_size := xs.size - recInfo.numMinors - recInfo.numIndices - 1
      let vs :=
        xs[*...AC_size] ++
        xs[(AC_size + recInfo.numMinors)...(AC_size + recInfo.numMinors + 1 + recInfo.numIndices)] ++
        xs[(AC_size)...(AC_size + recInfo.numMinors)]
      let type ← mkForallFVars vs t
      let value ← mkLambdaFVars vs e
      mkDefinitionValInferringUnsafe (mkRecOnName n) recInfo.levelParams type value .abbrev

  addDecl (.defnDecl decl)
  setReducibleAttribute decl.name
  modifyEnv fun env => markAuxRecursor env decl.name
  modifyEnv fun env => addProtected env decl.name

end Lean
