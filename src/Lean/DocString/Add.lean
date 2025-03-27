/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/

prelude
import Lean.Environment
import Lean.Exception
import Lean.Log
import Lean.DocString.Extension
import Lean.DocString.Links

set_option linter.missingDocs true

namespace Lean

/--
Validates all links to the Lean reference manual in `docstring`.

This is intended to be used before saving a docstring that is later subject to rewriting with
`rewriteManualLinks`.
-/
def validateDocComment
    [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m] [MonadLiftT IO m]
    (docstring : TSyntax `Lean.Parser.Command.docComment) :
    m Unit := do
  let str := docstring.getDocString
  let pos? := docstring.raw[1].getHeadInfo? >>= (·.getPos?)

  let (errs, out) ← (rewriteManualLinksCore str : IO _)

  for (⟨start, stop⟩, err) in errs do
    -- Report errors at their actual location if possible
    if let some pos := pos? then
      let urlStx : Syntax := .atom (.synthetic (pos + start) (pos + stop)) (str.extract start stop)
      logErrorAt urlStx err
    else
      logError err

/--
Adds a docstring to the environment, validating documentation links.
-/
def addDocString
    [Monad m] [MonadError m] [MonadEnv m] [MonadLog m] [AddMessageContext m] [MonadOptions m] [MonadLiftT IO m]
    (declName : Name) (docComment : TSyntax `Lean.Parser.Command.docComment) : m Unit := do
  unless (← getEnv).getModuleIdxFor? declName |>.isNone do
    throwError s!"invalid doc string, declaration '{declName}' is in an imported module"
  validateDocComment docComment
  let docString : String ← getDocStringText docComment
  modifyEnv fun env => docStringExt.insert env declName docString.removeLeadingSpaces

/--
Adds a docstring to the environment, validating documentation links.
-/
def addDocString'
    [Monad m] [MonadError m] [MonadEnv m] [MonadLog m] [AddMessageContext m] [MonadOptions m] [MonadLiftT IO m]
    (declName : Name) (docString? : Option (TSyntax `Lean.Parser.Command.docComment)) : m Unit :=
  match docString? with
  | some docString => addDocString declName docString
  | none => return ()
