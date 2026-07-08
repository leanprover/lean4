/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: David Thrane Christiansen
-/
import Lean.DocString.Parser

/-!
This file tests the Verso parser.

Input files are expected to be snippets of code; their filename picks which parser is used.
-/

open Lean Doc Parser

def ppSyntax (stx : Syntax) : Std.Format := .nest 2 <| stx.formatStx (some 50) false

open Std Format in
def ppStack (elts : Array Syntax) (number : Bool := false) : Format := Id.run do
  let mut stk : Format := .nil
  if h : elts.size = 0 then
    stk := " empty"
  else if elts.size = 1 then
    stk := "  " ++ ppSyntax elts[0]
  else
    for h : i in [0:elts.size] do
      let tm := ppSyntax (elts[i])
      let num := if number then .text s!"[{i}] " else .nil
      stk := stk ++ .group (" • " ++ num ++ nest 2 (.group tm)) ++ line
  pure stk

def test (p : ParserFn) (input : String) : IO String := do
  let ictx := mkInputContext input "<input>"
  let env : Environment ← mkEmptyEnvironment
  let pmctx : ParserModuleContext := {env := env, options := {}}
  let s' := p.run ictx pmctx (getTokenTable env) (mkParserState input)
  let stk := ppStack <| s'.stxStack.extract 0 s'.stxStack.size

  let remaining : String :=
    if s'.pos ≥ input.rawEndPos then "All input consumed."
    else s!"Remaining:\n{repr (s'.pos.extract input input.rawEndPos)}"

  if s'.allErrors.isEmpty then
    return s!"Success! Final stack:\n{stk.pretty 50}\n{remaining}"
  else if let #[(p, _, err)] := s'.allErrors then
    return s!"Failure @{p} ({ictx.fileMap.toPosition p}): {toString err}\n\
      Final stack:\n\
      {stk.pretty 50}\n\
      Remaining: {repr $ p.extract input input.rawEndPos}"
  else
    let mut errors := ""
    for (p, _, e) in s'.allErrors.qsort errLt do
      errors :=
        errors ++
        s!"  @{p} ({ictx.fileMap.toPosition p}): {toString e}\n" ++
        s!"    {repr <| p.extract input input.rawEndPos}\n"
    return s!"{s'.allErrors.size} failures:\n{errors}\nFinal stack:\n{stk.pretty 50}"
where
  errLt (x y : String.Pos.Raw × SyntaxStack × Error) : Bool :=
    let (p1, _, e1) := x
    let (p2, _, e2) := y
    p1 < p2 || p1 == p2 && toString e1 < toString e2

/--
The test case's filename determines which parser will be used to test it.
-/
def testConfigs : List (String × ParserFn):= [
  ("metadataBlock", metadataBlock),
  ("arg_val", val),
  ("arg", arg),
  ("args", args),
  ("nameAndArgs", nameAndArgs),
  ("inlineTextChar", inlineTextChar),
  ("manyInlineTextChar", (asStringFn (many1Fn inlineTextChar))),
  ("text", text),
  ("emph", (emph {})),
  ("code", code),
  ("role", (role {})),
  ("oneInline", (inline {})),
  ("codeBlock", (codeBlock {})),
  ("header", (header {})),
  ("blocks", (blocks {})),
  ("recoverBlock", (recoverBlock (block {}))),
  ("recoverBlocks", (recoverBlock (blocks {}))),
  ("directive", (directive {})),
  ("blockOpener", (ignoreFn blockOpener)),
  ("lookaheadUnorderedListIndicator",
    lookaheadUnorderedListIndicator {} (fun type => fakeAtom s! "{repr type}")),
  ("lookaheadOrderedListIndicator",
    lookaheadOrderedListIndicator {} (fun type i => fakeAtom s! "{repr type} {i}")),
  ("block", (block {})),
  ("document", document),
]

def main : List String → IO UInt32
  | [inputFile] => do
    let inputFile : System.FilePath := inputFile
    if inputFile.isAbsolute then
      IO.eprintln s!"Expected a relative path, got {inputFile}"
      return 2
    unless (← inputFile.pathExists) do
      IO.eprintln s!"File not found: {inputFile}"
      return 3
    let [file] := inputFile.components
      | IO.eprintln "Expected file in current directory"
        return 4
    let kind := file.takeWhile (· != '_')
    let some p := testConfigs.lookup kind.copy
      | IO.eprintln s!"Not found in test configs: {kind}"
        return 5
    IO.print <| ← test p (← IO.FS.readFile inputFile)
    return 0
  | args => do
    IO.eprintln s!"Expected precisely one argument, got {args}"
    return 1
