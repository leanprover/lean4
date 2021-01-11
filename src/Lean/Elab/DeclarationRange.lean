/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.DeclarationRange
import Lean.Elab.Log

namespace Lean.Elab

def getDeclarationRange [Monad m] [MonadFileMap m] (stx : Syntax) : m DeclarationRange := do
  let pos    := stx.getPos.getD 0
  let endPos := stx.getTailPos.getD pos
  let fileMap ← getFileMap
  return { pos := fileMap.toPosition pos, endPos := fileMap.toPosition endPos }

/--
  For most declarations, the selection range is just its name, which is stored in the second position.
  Example:
  ```
  "def " >> declId >> optDeclSig >> declVal
  ``` -/
def getDeclarationSelectionRangeDefault [Monad m] [MonadFileMap m] (stx : Syntax) : m DeclarationRange :=
  getDeclarationRange stx[1]


/--
  For instances, we use the whole declaration header as the selection range since the name is optional.
  ```
  Term.attrKind >> "instance " >> optNamedPrio >> optional declId >> declSig >> declVal
  ``` -/
def getInstanceSelectionRange [Monad m] [MonadFileMap m] (stx : Syntax) : m DeclarationRange :=
  getDeclarationRange <| stx.setArg 5 mkNullNode

/--
  Store the `range` and `selectionRange` for `declName` where `stx` is the whole syntax object decribing `declName`.
  This method is for the builtin declarations only.
  User-defined commands should use `Lean.addDeclarationRanges` to store this information for their commands. -/
def addDeclarationRanges [Monad m] [MonadEnv m] [MonadFileMap m] (declName : Name) (stx : Syntax) : m Unit := do
  if stx.getKind == ``Parser.Command.«example» then
    return ()
  else
    let selRange ←
      if stx.getKind == ``Parser.Command.«instance» then
        getInstanceSelectionRange stx
      else
        getDeclarationSelectionRangeDefault stx
    Lean.addDeclarationRanges declName {
      range          := (← getDeclarationRange stx)
      selectionRange := selRange
    }

/-- Auxiliary method for recording ranges for auxiliary declarations (e.g., fields, nested declarations, etc. -/
def addAuxDeclarationRanges [Monad m] [MonadEnv m] [MonadFileMap m] (declName : Name) (stx : Syntax) (header : Syntax) : m Unit := do
  Lean.addDeclarationRanges declName {
    range          := (← getDeclarationRange stx)
    selectionRange := (← getDeclarationRange header)
  }

end Lean.Elab
