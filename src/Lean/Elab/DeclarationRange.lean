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
  return some <| .ofStringPositions fileMap range.start range.stop

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
Derives and adds declaration ranges from given syntax trees. If `rangeStx` does not have a range,
nothing is added. If `selectionRangeStx` does not have a range, it is defaulted to that of
`rangeStx`.
-/
def addDeclarationRangesFromSyntax [Monad m] [MonadEnv m] [MonadFileMap m] (declName : Name)
    (rangeStx : Syntax) (selectionRangeStx : Syntax := .missing) : m Unit := do
  -- may fail on partial syntax, ignore in that case
  let some range ← getDeclarationRange? rangeStx | return
  let selectionRange ← (·.getD range) <$> getDeclarationRange? selectionRangeStx
  Lean.addDeclarationRanges declName { range, selectionRange }

/--
Stores the `range` and `selectionRange` for `declName` where `modsStx` is the modifier part and
`cmdStx` the remaining part of the syntax tree for `declName`.

This method is for the builtin declarations only. User-defined commands should use
`Lean.Elab.addDeclarationRangesFromSyntax` or `Lean.addDeclarationRanges` to store this information
for their commands.
-/
def addDeclarationRangesForBuiltin [Monad m] [MonadEnv m] [MonadFileMap m] (declName : Name)
    (modsStx : TSyntax ``Parser.Command.declModifiers) (declStx : Syntax) : m Unit := do
  if declStx.getKind == ``Parser.Command.«example» then
    return ()
  let stx := mkNullNode #[modsStx, declStx]
  addDeclarationRangesFromSyntax declName stx (getDeclarationSelectionRef declStx)

end Lean.Elab
