/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Lean
open Lean Elab PrettyPrinter

partial def getCommands (cmds : Syntax) : StateT (Array Syntax) Id Unit := do
  if cmds.getKind == nullKind || cmds.getKind == ``Parser.Module.header then
    for cmd in cmds.getArgs do
      getCommands cmd
  else
    modify (·.push cmds)

partial def reprintCore : Syntax → Option Format
  | Syntax.missing => none
  | Syntax.atom _ val => val.trim
  | Syntax.ident _ rawVal _ _ => rawVal.toString
  | Syntax.node _ kind args =>
    match args.toList.filterMap reprintCore with
    | [] => none
    | [arg] => arg
    | args => Format.group <| Format.nest 2 <| Format.line.joinSep args

def reprint (stx : Syntax) : Format :=
  reprintCore stx |>.getD ""

def printCommands (cmds : Syntax) : CoreM Unit := do
  for cmd in getCommands cmds |>.run #[] |>.2 do
    try
      IO.println (← ppCommand cmd).pretty
    catch e =>
      IO.println f!"/-\ncannot print: {← e.toMessageData.format}\n{reprint cmd}\n-/"

def failWith (msg : String) (exitCode : UInt8 := 1) : IO α := do
  (← IO.getStderr).putStrLn msg
  IO.Process.exit exitCode

structure CommandSyntax where
  env : Environment
  currNamespace : Name := Name.anonymous
  openDecls : List OpenDecl := []
  stx : Syntax

def parseModule (input : String) (fileName : String) (opts : Options := {}) (trustLevel : UInt32 := 1024) :
    IO <| Array CommandSyntax := do
  let mainModuleName := Name.anonymous -- FIXME
  let inputCtx := Parser.mkInputContext input fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header opts messages inputCtx trustLevel
  let env := env.setMainModule mainModuleName
  let env0 := env
  let s ← IO.processCommands inputCtx parserState
    { Command.mkState env messages opts with infoState := { enabled := true } }
  let topLevelCmds : Array CommandSyntax ← s.commandState.infoState.trees.toArray.mapM fun
    | InfoTree.context { env, currNamespace, openDecls, .. }
        (InfoTree.node (Info.ofCommandInfo {stx, ..}) _) =>
      pure {env, currNamespace, openDecls, stx}
    | _ =>
      failWith "unknown info tree"
  #[{ env := env0, stx := header : CommandSyntax }] ++ topLevelCmds

unsafe def main (args : List String) : IO Unit := do
  let [fileName] ← args | failWith "Usage: reformat file"
  let input ← IO.FS.readFile fileName
  let moduleStx ← parseModule input fileName
  let leadingUpdated := mkNullNode (moduleStx.map (·.stx)) |>.updateLeading |>.getArgs
  let mut first := true
  for {env, currNamespace, openDecls, ..} in moduleStx, stx in leadingUpdated do
    if first then first := false else IO.print "\n"
    let _ ← printCommands stx |>.toIO {currNamespace, openDecls} {env}
