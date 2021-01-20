/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.DeclarationRange
import Lean.Elab.Log
import Lean.Data.Lsp.Utf16

namespace Lean.Elab

def getDeclarationRange [Monad m] [MonadFileMap m] (stx : Syntax) : m DeclarationRange := do
  let fileMap ← getFileMap
  let pos    := stx.getPos?.getD 0
  let endPos := stx.getTailPos?.getD pos |> fileMap.toPosition
  let pos    := pos |> fileMap.toPosition
  return {
    pos          := pos
    charUtf16    := fileMap.leanPosToLspPos pos |>.character
    endPos       := endPos
    endCharUtf16 := fileMap.leanPosToLspPos endPos |>.character
  }

/--
  For most builtin declarations, the selection range is just its name, which is stored in the second position.
  Example:
  ```
  "def " >> declId >> optDeclSig >> declVal
  ```
  For instances, we use the whole header since the name is optional.
  This function converts the given `Syntax` into one that represents its "selection range".
-/
def getDeclarationSelectionRef (stx : Syntax) : Syntax :=
  if stx.getKind == ``Parser.Command.«instance» then
    stx.setArg 5 mkNullNode
  else
    stx[1]

/--
  Store the `range` and `selectionRange` for `declName` where `stx` is the whole syntax object decribing `declName`.
  This method is for the builtin declarations only.
  User-defined commands should use `Lean.addDeclarationRanges` to store this information for their commands. -/
def addDeclarationRanges [Monad m] [MonadEnv m] [MonadFileMap m] (declName : Name) (stx : Syntax) : m Unit := do
  if stx.getKind == ``Parser.Command.«example» then
    return ()
  else
    Lean.addDeclarationRanges declName {
      range          := (← getDeclarationRange stx)
      selectionRange := (← getDeclarationRange (getDeclarationSelectionRef stx))
    }

/-- Auxiliary method for recording ranges for auxiliary declarations (e.g., fields, nested declarations, etc. -/
def addAuxDeclarationRanges [Monad m] [MonadEnv m] [MonadFileMap m] (declName : Name) (stx : Syntax) (header : Syntax) : m Unit := do
  Lean.addDeclarationRanges declName {
    range          := (← getDeclarationRange stx)
    selectionRange := (← getDeclarationRange header)
  }

end Lean.Elab
