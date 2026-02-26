/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Lean.PrettyPrinter
import Lean.Elab.Import
import Lean.Elab.Command

namespace Lean.PrettyPrinter

private def isCommentOrBlankLine (line : String) : Bool :=
  let trimmed := line.trimAsciiStart
  trimmed.isEmpty || trimmed.startsWith "--"

/-- Strip trailing lines that are pure comments or blank from ppCommand output.
The formatter's `pushToken` preserves trailing `SourceInfo` comments at incorrect
indentation (nested under the last expression). The gap extraction re-includes them
at their correct original indentation.
Scans backward from the end so only trailing lines are inspected. -/
public def trimTrailingCommentLines (s : String) : String :=
  let lines := s.split '\n' |>.toStringList
  let kept := lines.reverse.dropWhile isCommentOrBlankLine |>.reverse
  "\n".intercalate kept

/-- Collapse runs of 3+ consecutive newlines down to 2 (at most one blank line).
Folds over characters, tracking consecutive newline count. -/
public def collapseBlankLines (s : String) : String :=
  let (acc, _) := s.foldl (fun (acc, nlCount) c =>
    if c == '\n' then
      if nlCount < 2 then (acc.push '\n', nlCount + 1)
      else (acc, nlCount)
    else
      (acc.push c, 0)) ("", 0)
  acc

/-- Parse all top-level commands from an input context. -/
private partial def parseCommands (inputCtx : Parser.InputContext) (pmctx : Parser.ParserModuleContext)
    (parserState : Parser.ModuleParserState) : Array Syntax :=
  go parserState {} #[]
where
  go (mps : Parser.ModuleParserState) (msgs : MessageLog) (acc : Array Syntax) : Array Syntax :=
    let (stx, mps', msgs') := Parser.parseCommand inputCtx pmctx mps msgs
    if Parser.isTerminalCommand stx then acc
    else go mps' msgs' (acc.push stx)

/-- Extract the inter-command gap from original source, collapsing excessive blank lines. -/
private def interCommandGap (contents : String) (prevTailPos : Option String.Pos.Raw)
    (curStartPos : Option String.Pos.Raw) : String :=
  match prevTailPos, curStartPos with
  | some prevEnd, some curStart => collapseBlankLines (String.Pos.Raw.extract contents prevEnd curStart)
  | none, some curStart       => collapseBlankLines (String.Pos.Raw.extract contents {} curStart)
  | _, none                     => "\n"

/-- Extract the header text from original source, trimming trailing whitespace. -/
private def extractHeader (contents : String) (headerStx : Syntax) : String :=
  let raw := match headerStx.getPos?, headerStx.getTailPos? with
    | some s, some e => String.Pos.Raw.extract contents s e
    | _, _           => headerStx.reprint.getD ""
  raw.trimAsciiEnd.copy

/-- Pretty-print a single command, falling back to reprint on error. -/
private def ppSingleCommand (stx : Syntax) (cmdState : Elab.Command.State)
    (fileName : String) (fileMap : FileMap) : IO String := do
  let cmdCtx : Elab.Command.Context := {
    cmdPos := stx.getPos?.getD 0
    fileName, fileMap
    snap? := none, cancelTk? := none
  }
  let fmtResult ← (Elab.Command.liftCoreM (ppCommand ⟨stx⟩) |>.run cmdCtx |>.run' cmdState).toBaseIO
  return match fmtResult with
    | .ok fmt  => trimTrailingCommentLines fmt.pretty.trimAsciiEnd.copy
    | .error _ => trimTrailingCommentLines (stx.reprint.getD "").trimAsciiEnd.copy

/-- Pretty-print a Lean source file. Parses the header and commands,
then pretty-prints each command via `ppCommand`. Only requires parsing,
not elaboration. Returns the formatted source text. -/
public def ppSource (contents : String) (fileName : String) (opts : Options := {}) : IO String := do
  let inputCtx := Parser.mkInputContext contents fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, _) ← Elab.processHeader header opts messages inputCtx (trustLevel := 1024)
  let pmctx : Parser.ParserModuleContext := { env, options := opts }
  let cmdStxs := parseCommands inputCtx pmctx parserState
  let cmdState := Elab.Command.mkState env {} opts
  let fileMap := FileMap.ofString contents
  let mut result := extractHeader contents header.raw
  let mut prevTailPos := header.raw.getTailPos?
  for stx in cmdStxs do
    result := result ++ interCommandGap contents prevTailPos stx.getPos?
    result := result ++ (← ppSingleCommand stx cmdState fileName fileMap)
    prevTailPos := stx.getTailPos?
  if !result.isEmpty && !result.endsWith "\n" then
    result := result ++ "\n"
  return result

end Lean.PrettyPrinter
