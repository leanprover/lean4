/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Lean.Elab.Tactic.Basic
public import Lean.LibrarySuggestions.Basic
public import Init.System.IO

public section

namespace Lean.Elab.Tactic.Claude

open Lean Meta Elab.Tactic

/-! ## Template Parsing and Interpolation -/

structure Template where
  content : String
  variables : Array String  -- Variables referenced in template
  deriving Inhabited

/-- Extract variable names from template (e.g., `{goal}` → "goal") -/
def extractVariables (content : String) : Array String :=
  -- Check for each known variable
  let knownVars := #["goal", "declaration", "file_prefix", "suggestions", "suggestions_types", "lean_version"]
  knownVars.filter fun varName =>
    content.contains s!"\{{varName}}"

/-- Parse template to identify referenced variables -/
def parseTemplate (content : String) : Template :=
  { content := content, variables := extractVariables content }

/-- Default template embedded at compile time (with code fences) -/
def defaultTemplateContent : String :=
  include_str "default_template.txt"

/-- Load template from file or use default -/
def loadTemplateContent (templatePath : String) : IO String := do
  if templatePath.isEmpty then
    -- Use embedded default template
    return defaultTemplateContent
  else
    -- Use custom template
    let path : System.FilePath := ⟨templatePath⟩
    if ← path.pathExists then
      IO.FS.readFile templatePath
    else
      throw <| IO.userError s!"Template file not found: {templatePath}"

/-! ## Template Variable Computation -/

/-- Context for template variable evaluation (lazy) -/
structure TemplateContext where
  goal : Unit → TacticM String
  declaration : Unit → TacticM String
  filePrefix : Unit → TacticM String
  suggestions : Unit → TacticM String
  suggestionsTypes : Unit → TacticM String
  leanVersion : Unit → TacticM String

/-- Get pretty-printed goal -/
def getGoalString (mvarId : MVarId) : TacticM String := do
  return toString (← Meta.ppGoal mvarId)

/-- Find start of declaration by searching backwards for keywords -/
def findDeclStart (source : String) (posIdx : Nat) : Nat := Id.run do
  let declKeywords := #["theorem", "lemma", "def", "example", "instance", "structure", "inductive", "class", "abbrev"]
  let bytes := source.toUTF8
  let posIdx := min posIdx bytes.size
  let mut searchIdx := posIdx
  let mut declStart : Nat := 0

  while searchIdx > 0 do
    -- Find start of current line (scan backwards for newline byte 0x0A)
    let mut lineStart := searchIdx
    while lineStart > 0 && bytes.get! (lineStart - 1) != 0x0A do
      lineStart := lineStart - 1

    -- Check if line starts with a declaration keyword (possibly after whitespace)
    let endIdx := min (lineStart + 50) bytes.size
    let linePrefix := (String.Pos.Raw.extract source ⟨lineStart⟩ ⟨endIdx⟩).trimAscii.toString
    let foundDecl := declKeywords.any fun kw =>
      linePrefix.startsWith kw &&
        (linePrefix.length == kw.length ||
         (kw.length < linePrefix.length && !(String.Pos.Raw.get linePrefix ⟨kw.length⟩).isAlphanum))

    if foundDecl then
      declStart := lineStart
      break

    if lineStart > 0 then
      searchIdx := lineStart - 1
    else
      break

  return declStart

/-- Get current declaration source text, with `sorry` replacing the current tactic position -/
def getDeclarationString : TacticM String := do
  let fileMap ← getFileMap
  let ref ← getRef
  let some pos := ref.getPos?
    | return ""

  let source := fileMap.source
  let posIdx := pos.byteIdx
  let declStart := findDeclStart source posIdx

  if declStart < posIdx then
    -- Extract declaration up to the current position, then append `sorry`
    let declPrefix := String.Pos.Raw.extract source ⟨declStart⟩ ⟨posIdx⟩
    return declPrefix ++ "sorry"
  else
    return ""

/-- Maximum number of lines for file prefix -/
def maxFilePrefixLines : Nat := 1000

/-- Find the start position to include at most n lines before endIdx -/
def findLineStart (source : String) (endIdx : Nat) (maxLines : Nat) : Nat := Id.run do
  if endIdx == 0 then return 0
  -- Use raw bytes for safe access (newline is always a single byte 0x0A in UTF-8)
  let bytes := source.toUTF8
  let endIdx := min endIdx bytes.size
  if endIdx == 0 then return 0

  let mut idx := endIdx
  let mut linesFound : Nat := 0

  -- Move backwards counting newlines (0x0A = '\n')
  while idx > 0 && linesFound < maxLines do
    idx := idx - 1
    if bytes.get! idx == 0x0A then
      linesFound := linesFound + 1

  -- If we hit the start, return 0; otherwise return position after the newline we stopped at
  if idx == 0 then 0 else idx + 1

/-- Get file content before current declaration (bounded by line count) -/
def getFilePrefixString : TacticM String := do
  let fileMap ← getFileMap
  let ref ← getRef
  let some pos := ref.getPos?
    | return ""

  let source := fileMap.source
  let posIdx := pos.byteIdx

  -- Find where the current declaration starts
  let declStart := findDeclStart source posIdx

  -- If declaration is at start of file, no prefix
  if declStart == 0 then
    return ""

  -- Get content before declaration, limited to maxFilePrefixLines
  let startIdx := findLineStart source declStart maxFilePrefixLines

  let content := String.Pos.Raw.extract source ⟨startIdx⟩ ⟨declStart⟩

  -- Trim trailing whitespace (blank lines before declaration)
  return content.trimAsciiEnd.toString

/-- Get library suggestions as formatted string -/
def getLibrarySuggestionsString (mvarId : MVarId) : TacticM String := do
  try
    let suggestions ← LibrarySuggestions.select mvarId {}
    if suggestions.isEmpty then
      return ""
    let mut result := ""
    for s in suggestions do
      result := result ++ s!"- {s.name} (score: {s.score})\n"
    return result
  catch _ =>
    -- If library suggestions fail, return empty
    return ""

/-- Get library suggestions with types -/
def getLibrarySuggestionsWithTypes (mvarId : MVarId) : TacticM String := do
  try
    let suggestions ← LibrarySuggestions.select mvarId {}
    if suggestions.isEmpty then
      return ""
    let mut result := ""
    for s in suggestions do
      try
        let info ← getConstInfo s.name
        result := result ++ s!"- {s.name} : {info.type} (score: {s.score})\n"
      catch _ =>
        result := result ++ s!"- {s.name} (score: {s.score})\n"
    return result
  catch _ =>
    return ""

/-- Build template context with lazy evaluation -/
def buildTemplateContext (mvarId : MVarId) : TacticM TemplateContext := do
  return {
    goal := fun () => getGoalString mvarId
    declaration := fun () => getDeclarationString
    filePrefix := fun () => getFilePrefixString
    suggestions := fun () => getLibrarySuggestionsString mvarId
    suggestionsTypes := fun () => getLibrarySuggestionsWithTypes mvarId
    leanVersion := fun () => pure Lean.versionString
  }

/-- Interpolate template with context (only evaluates referenced variables) -/
def interpolateTemplate (template : Template) (ctx : TemplateContext) : TacticM String := do
  let mut result := template.content

  for varName in template.variables do
    let value ← match varName with
      | "goal" => ctx.goal ()
      | "declaration" => ctx.declaration ()
      | "file_prefix" => ctx.filePrefix ()
      | "suggestions" => ctx.suggestions ()
      | "suggestions_types" => ctx.suggestionsTypes ()
      | "lean_version" => ctx.leanVersion ()
      | _ => pure ""  -- Unknown variable, ignore

    -- Replace {varName} with value
    result := result.replace s!"\{{varName}}" value

  return result

end Lean.Elab.Tactic.Claude
