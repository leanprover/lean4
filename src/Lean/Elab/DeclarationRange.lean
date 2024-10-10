/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Log
import Lean.Parser.Command
import Lean.DeclarationRange
import Lean.Data.Lsp.Utf16

namespace Lean.Elab

def getDeclarationRange? [Monad m] [MonadFileMap m] (stx : Syntax) : m (Option DeclarationRange) := do
  let some range := stx.getRange?
    | return none
  let fileMap ← getFileMap
  --let range := fileMap.utf8RangeToLspRange
  let pos    := fileMap.toPosition range.start
  let endPos := fileMap.toPosition range.stop
  return some {
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
Stores the `range` and `selectionRange` for `declName` where `modsStx` is the modifier part and
`cmdStx` the remaining part of the syntax tree for `declName`.

This method is for the builtin declarations only. User-defined commands should use
`Lean.addDeclarationRanges` to store this information for their commands.
-/
def addDeclarationRanges [Monad m] [MonadEnv m] [MonadFileMap m] (declName : Name)
    (modsStx : TSyntax ``Parser.Command.declModifiers) (declStx : Syntax) : m Unit := do
  if declStx.getKind == ``Parser.Command.«example» then
    return ()
  let stx := mkNullNode #[modsStx, declStx]
  -- may fail on partial syntax, ignore in that case
  let some range ← getDeclarationRange? stx | return
  let some selectionRange ← getDeclarationRange? (getDeclarationSelectionRef declStx) | return
  Lean.addDeclarationRanges declName { range, selectionRange }

/-- Auxiliary method for recording ranges for auxiliary declarations (e.g., fields, nested declarations, etc. -/
def addAuxDeclarationRanges [Monad m] [MonadEnv m] [MonadFileMap m] (declName : Name) (stx : Syntax) (header : Syntax) : m Unit := do
  -- may fail on partial syntax, ignore in that case
  let some range ← getDeclarationRange? stx | return
  let some selectionRange ← getDeclarationRange? header | return
  Lean.addDeclarationRanges declName { range, selectionRange }

end Lean.Elab
