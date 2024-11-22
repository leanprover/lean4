/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Huisinga
-/
prelude
import Lean.Data.NameTrie
import Lean.Util.Paths
import Lean.Util.LakePath
import Lean.Server.Completion.CompletionItemData

namespace ImportCompletion

open Lean Lsp

abbrev ImportTrie := Lean.NameTrie Name

abbrev AvailableImports := Array Name

def AvailableImports.toImportTrie (imports : AvailableImports) : ImportTrie := Id.run do
  let mut importTrie := ∅
  for i in imports do
    importTrie := importTrie.insert i i
  return importTrie

def determinePartialHeaderCompletions
    (headerStx : Syntax)
    (completionPos : String.Pos)
    : Option Syntax := Id.run do
  let some importCmdToComplete := headerStx[1].find? fun importStx => Id.run do
      let importIdStx := importStx
      let some startPos := importIdStx.getPos?
        | return false
      let some endPos := importIdStx.getTailPos?
        | return false
      return startPos <= completionPos && completionPos <= endPos
    | return none
  return some importCmdToComplete

/-- Checks whether `completionPos` points at the position after an incomplete `import` statement. -/
def isImportNameCompletionRequest (headerStx : Syntax) (completionPos : String.Pos) : Bool :=
  headerStx[1].getArgs.any fun importStx =>
    let importCmd := importStx[0]
    let importId := importStx[2]
    importId.isMissing && importCmd.getTailPos?.isSome && completionPos == importCmd.getTailPos?.get! + ' '

/-- Checks whether `completionPos` points at a free space in the header. -/
def isImportCmdCompletionRequest (headerStx : Syntax) (completionPos : String.Pos) : Bool :=
  ! headerStx[1].getArgs.any fun importStx => importStx.getArgs.any fun arg =>
    arg.getPos?.isSome && arg.getTailPos?.isSome
      && arg.getPos?.get! <= completionPos && completionPos <= arg.getTailPos?.get!

def computePartialImportCompletions
    (headerStx : Syntax)
    (completionPos : String.Pos)
    (availableImports : ImportTrie)
    : Array Name := Id.run do
  let some (completePrefix, incompleteSuffix) := headerStx[1].getArgs.findSome? fun importStx => do
      -- `partialTrailingDotStx` ≙ `("." ident)?`
      let partialTrailingDotStx := importStx[3]
      if ! partialTrailingDotStx.hasArgs then
        let tailPos ← importStx[2].getTailPos?
        guard <| tailPos == completionPos
        let .str completePrefix incompleteSuffix := importStx[2].getId
          | none
        return (completePrefix, incompleteSuffix)
      else
        let trailingDot := partialTrailingDotStx[0]
        let tailPos ← trailingDot.getTailPos?
        guard <| tailPos == completionPos
        return (importStx[2].getId, "")
    | return #[]

  let completions := availableImports.matchingToArray completePrefix
    |>.map (·.replacePrefix completePrefix .anonymous)
    |>.filter (·.toString.startsWith incompleteSuffix)
    |>.filter (! ·.isAnonymous)
    |>.qsort Name.quickLt

  return completions


def isImportCompletionRequest (text : FileMap) (headerStx : Syntax) (params : CompletionParams) : Bool :=
  let completionPos := text.lspPosToUtf8Pos params.position
  let headerStartPos := headerStx.getPos?.getD 0
  let headerEndPos := headerStx.getTailPos?.getD headerStartPos
  completionPos <= headerEndPos + ' ' + ' '

def collectAvailableImportsFromLake : IO (Option AvailableImports) := do
  let lakePath ← Lean.determineLakePath
  let spawnArgs : IO.Process.SpawnArgs := {
    stdin  := IO.Process.Stdio.null
    stdout := IO.Process.Stdio.piped
    stderr := IO.Process.Stdio.piped
    cmd    := lakePath.toString
    args   := #["available-imports"]
  }
  let lakeProc ← IO.Process.spawn spawnArgs
  let stdout := String.trim (← lakeProc.stdout.readToEnd)
  let exitCode ← lakeProc.wait
  match exitCode with
  | 0 =>
    let Except.ok (availableImports : AvailableImports) := Json.parse stdout >>= fromJson?
      | throw <| IO.userError  s!"invalid output from `lake available-imports`:\n{stdout}"
    return availableImports
  | _ =>
    return none

def collectAvailableImportsFromSrcSearchPath : IO AvailableImports :=
  (·.2) <$> StateT.run (s := #[]) do
    let srcSearchPath ← initSrcSearchPath
    for p in srcSearchPath do
      if ! (← p.isDir) then
        continue
      Lean.forEachModuleInDir p fun mod => do
        modify (·.push mod)

def collectAvailableImports : IO AvailableImports := do
  match ← ImportCompletion.collectAvailableImportsFromLake with
  | none =>
    -- lake is not available => walk LEAN_SRC_PATH for an approximation
    ImportCompletion.collectAvailableImportsFromSrcSearchPath
  | some availableImports => pure availableImports

/--
Sets the `data?` field of every `CompletionItem` in `completionList` using `params`. Ensures that
`completionItem/resolve` requests can be routed to the correct file worker even for
`CompletionItem`s produced by the import completion.
-/
def addCompletionItemData (completionList : CompletionList) (params : CompletionParams)
    : CompletionList :=
  let data := { params : Lean.Lsp.CompletionItemData }
  { completionList with items := completionList.items.map fun item =>
    { item with data? := some <| toJson data } }

def find (text : FileMap) (headerStx : Syntax) (params : CompletionParams) (availableImports : AvailableImports) : CompletionList :=
  let availableImports := availableImports.toImportTrie
  let completionPos := text.lspPosToUtf8Pos params.position
  if isImportNameCompletionRequest headerStx completionPos then
    let allAvailableImportNameCompletions := availableImports.toArray.map ({ label := toString · })
    addCompletionItemData { isIncomplete := false, items := allAvailableImportNameCompletions } params
  else if isImportCmdCompletionRequest headerStx completionPos then
    let allAvailableFullImportCompletions := availableImports.toArray.map ({ label := s!"import {·}" })
    addCompletionItemData { isIncomplete := false, items := allAvailableFullImportCompletions } params
  else
    let completionNames : Array Name := computePartialImportCompletions headerStx completionPos availableImports
    let completions : Array CompletionItem := completionNames.map ({ label := toString · })
    addCompletionItemData { isIncomplete := false, items := completions } params

def computeCompletions (text : FileMap) (headerStx : Syntax) (params : CompletionParams)
    : IO CompletionList := do
  let availableImports ← collectAvailableImports
  let completionList := find text headerStx params availableImports
  return addCompletionItemData completionList params

end ImportCompletion
