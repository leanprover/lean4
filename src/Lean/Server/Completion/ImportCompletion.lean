/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Huisinga
-/
module

prelude
public import Lean.Util.LakePath
public import Lean.Data.Lsp
public import Lean.Parser.Module
meta import Lean.Parser.Module
import Init.System.Uri

public section

namespace ImportCompletion

open Lean Lsp

abbrev ImportTrie := Lean.NameTrie Name

abbrev AvailableImports := Array Name

def AvailableImports.toImportTrie (imports : AvailableImports) : ImportTrie := Id.run do
  let mut importTrie := ∅
  for i in imports do
    importTrie := importTrie.insert i i
  return importTrie

def isImportNameCompletionRequest (headerStx : TSyntax ``Parser.Module.header) (completionPos : String.Pos.Raw) : Bool := Id.run do
  let `(Parser.Module.header| $[module]? $[prelude]? $importsStx*) := headerStx
    | return false
  return importsStx.any fun importStx => Id.run do
    let importStx := importStx.raw
    -- `importStx[0] == "private"?`
    -- `importStx[1] == "meta"?`
    let importCmd := importStx[2]
    let allTk? := importStx[3].getOptional?
    let importId := importStx[4]
    let keywordsTailPos := allTk?.bind (·.getTailPos?) <|> importCmd.getTailPos?
    return importId.isMissing && keywordsTailPos.isSome && completionPos == keywordsTailPos.get! + ' '

/-- Checks whether `completionPos` points at a free space in the header. -/
def isImportCmdCompletionRequest (headerStx : TSyntax ``Parser.Module.header) (completionPos : String.Pos.Raw) : Bool := Id.run do
  let `(Parser.Module.header| $[module]? $[prelude]? $importsStx*) := headerStx
    | return false
  return ! importsStx.any fun importStx => importStx.raw.getArgs.any fun arg =>
    arg.getPos?.isSome && arg.getTailPos?.isSome
      && arg.getPos?.get! <= completionPos && completionPos <= arg.getTailPos?.get!

def computePartialImportCompletions
    (headerStx : TSyntax ``Parser.Module.header)
    (completionPos : String.Pos.Raw)
    (availableImports : ImportTrie)
    : Array Name := Id.run do
  let `(Parser.Module.header| $[module]? $[prelude]? $importsStx*) := headerStx
    | return #[]
  let some (completePrefix, incompleteSuffix) := importsStx.findSome? fun importStx => do
      let `(Parser.Module.«import»| $[public]? $[meta]? import $[all]? $importId $[.%$trailingDotTk?$_]?) := importStx
        | unreachable!
      match trailingDotTk? with
      | none =>
        let tailPos ← importId.raw.getTailPos?
        guard <| tailPos == completionPos
        let .str completePrefix incompleteSuffix := importId.getId
          | none
        return (completePrefix, incompleteSuffix)
      | some trailingDotTk =>
        let tailPos ← trailingDotTk.getTailPos?
        guard <| tailPos == completionPos
        return (importId.getId, "")
    | return #[]

  let completions := availableImports.matchingToArray completePrefix
    |>.map (·.replacePrefix completePrefix .anonymous)
    |>.filter (·.toString.startsWith incompleteSuffix)
    |>.filter (! ·.isAnonymous)
    |>.qsort Name.quickLt

  return completions


def isImportCompletionRequest (text : FileMap) (headerStx : TSyntax ``Parser.Module.header) (params : CompletionParams) : Bool :=
  let completionPos := text.lspPosToUtf8Pos params.position
  let headerStartPos := headerStx.raw.getPos?.getD 0
  let headerEndPos := headerStx.raw.getTailPos?.getD headerStartPos
  completionPos <= headerEndPos + ' ' + ' '

def collectAvailableImportsFromLake (uri : DocumentUri) : IO (Option AvailableImports) := do
  let lakePath ← Lean.determineLakePath
  let filePath? := System.Uri.fileUriToPath? uri
  let spawnArgs : IO.Process.SpawnArgs := {
    stdin  := IO.Process.Stdio.null
    stdout := IO.Process.Stdio.piped
    stderr := IO.Process.Stdio.piped
    cmd    := lakePath.toString
    args   := #["available-imports"] ++ (filePath?.map (#[·.toString]) |>.getD #[])
  }
  -- TODO: implement
  let lakeProc ← IO.Process.spawn spawnArgs
  let stdout := String.trimAscii (← lakeProc.stdout.readToEnd) |>.copy
  let exitCode ← lakeProc.wait
  match exitCode with
  | 0 =>
    let Except.ok (availableImports : AvailableImports) := Json.parse stdout >>= fromJson?
      | throw <| IO.userError  s!"invalid output from `lake available-imports`:\n{stdout}"
    return availableImports
  | _ =>
    return none

def collectAvailableImports (uri : DocumentUri) : IO AvailableImports := do
  let some imports ← ImportCompletion.collectAvailableImportsFromLake uri
    | return #[]
  return imports

/--
Sets the `data?` field of every `CompletionItem` in `completionList` using `params`. Ensures that
`completionItem/resolve` requests can be routed to the correct file worker even for
`CompletionItem`s produced by the import completion.
-/
def addCompletionItemData (uri : DocumentUri) (pos : Lsp.Position) (completionList : CompletionList)
    : CompletionList :=
  let data := { uri, pos : Lean.Lsp.ResolvableCompletionItemData }
  { completionList with items := completionList.items.map fun item =>
    { item with data? := some <| toJson data } }

def find (uri : DocumentUri) (pos : Lsp.Position) (text : FileMap) (headerStx : TSyntax ``Parser.Module.header) (availableImports : AvailableImports) : CompletionList :=
  let availableImports := availableImports.toImportTrie
  let completionPos := text.lspPosToUtf8Pos pos
  if isImportNameCompletionRequest headerStx completionPos then
    let allAvailableImportNameCompletions := availableImports.toArray.map ({ label := toString · })
    addCompletionItemData uri pos { isIncomplete := false, items := allAvailableImportNameCompletions }
  else if isImportCmdCompletionRequest headerStx completionPos then
    let allAvailableFullImportCompletions := availableImports.toArray.map ({ label := s!"import {·}" })
    addCompletionItemData uri pos { isIncomplete := false, items := allAvailableFullImportCompletions }
  else
    let completionNames : Array Name := computePartialImportCompletions headerStx completionPos availableImports
    let completions : Array CompletionItem := completionNames.map ({ label := toString · })
    addCompletionItemData uri pos { isIncomplete := false, items := completions }

def computeCompletions (uri : DocumentUri) (pos : Lsp.Position) (text : FileMap) (headerStx : TSyntax ``Parser.Module.header)
    : IO CompletionList := do
  let availableImports ← collectAvailableImports uri
  let completionList := find uri pos text headerStx availableImports
  return addCompletionItemData uri pos completionList

end ImportCompletion
