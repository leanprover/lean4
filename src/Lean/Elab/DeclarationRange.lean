/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Log
import Lean.Parser.Command
import Lean.DeclarationRange
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
  If the declaration name is absent, we use the keyword instead.
  This function converts the given `Syntax` into one that represents its "selection range".
-/
def getDeclarationSelectionRef (stx : Syntax) : Syntax :=
  if stx.isOfKind ``Lean.Parser.Command.instance then
    -- must skip `attrKind` and `optPrio` for `instance`
    if !stx[3].isNone then
      stx[3][0]
    else
      stx[1]
  else
    if stx[1][0].isIdent then
      stx[1][0]  -- `declId`
    else if stx[1].isIdent then
      stx[1]  -- raw `ident`
    else
      stx[0]


/--
  Store the `range` and `selectionRange` for `declName` where `stx` is the whole syntax object describing `declName`.
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
