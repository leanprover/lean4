/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Lean.Elab.Command

public section

namespace Lean.Elab.Term.Doc
open Lean.Parser.Term.Doc
open Lean.Elab.Command
open Lean.Parser.Command

@[builtin_command_elab «recommended_spelling»] def elabRecommendedSpelling : CommandElab
  | `(«recommended_spelling»|$[$docs:docComment]? recommended_spelling $spelling:str for $«notation»:str in [$[$decls:ident],*]) => do
    let declNames ← liftTermElabM <| decls.mapM (fun decl => realizeGlobalConstNoOverloadWithInfo decl)
    declNames.forM (recordExtraModUseFromDecl (isMeta := false))
    let recommendedSpelling : RecommendedSpelling := {
      «notation» := «notation».getString
      recommendedSpelling := spelling.getString
      additionalInformation? := docs.map (·.getDocString)
    }
    modifyEnv (flatAddommendedSpelling · recommendedSpelling declNames)
  | _ => throwError "Malformed recommended spelling command"

/-- Returns an array containing all recommended spellings. -/
def allRecommendedSpellings : MetaM (Array RecommendedSpelling) := do
  let all := recommendedSpellingExt.toEnvExtension.getState (← getEnv)
      |>.importedEntries
      |>.push (recommendedSpellingExt.exportEntriesFn (← getEnv) (recommendedSpellingExt.getState (← getEnv)) .exported)
  return all.flatMap id

end Lean.Elab.Term.Doc
