/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Lean.Elab.Import
import Init.Lean.Elab.Command

namespace Lean
namespace Elab
namespace Frontend

structure Context :=
(commandStateRef : IO.Ref Command.State)
(parserStateRef  : IO.Ref Parser.ModuleParserState)
(cmdPosRef       : IO.Ref String.Pos)
(parserCtx       : Parser.ParserContextCore)

abbrev FrontendM := ReaderT Context (EIO Empty)

@[inline] def liftIOCore! {α} [Inhabited α] (x : IO α) : EIO Empty α :=
EIO.catchExceptions x (fun _ => unreachable!)

@[inline] def runCommandElabM (x : Command.CommandElabM Unit) : FrontendM Unit :=
fun ctx => do
  cmdPos ← liftIOCore! $ ctx.cmdPosRef.get;
  let cmdCtx : Command.Context := { cmdPos := cmdPos, stateRef := ctx.commandStateRef, fileName := ctx.parserCtx.fileName, fileMap := ctx.parserCtx.fileMap };
  EIO.catchExceptions (x cmdCtx) (fun _ => pure ())

def elabCommandAtFrontend (stx : Syntax) : FrontendM Unit :=
runCommandElabM (Command.withLogging $ Command.elabCommand stx)

def updateCmdPos : FrontendM Unit :=
fun ctx => do
  parserState ← liftIOCore! $ ctx.parserStateRef.get;
  liftIOCore! $ ctx.cmdPosRef.set parserState.pos

def getParserState : FrontendM Parser.ModuleParserState :=
fun ctx => liftIOCore! $ ctx.parserStateRef.get

def getCommandState : FrontendM Command.State :=
fun ctx => liftIOCore! $ ctx.commandStateRef.get

def setParserState (ps : Parser.ModuleParserState) : FrontendM Unit :=
fun ctx => liftIOCore! $ ctx.parserStateRef.set ps

def setMessages (msgs : MessageLog) : FrontendM Unit :=
fun ctx => liftIOCore! $ ctx.commandStateRef.modify $ fun s => { messages := msgs, .. s }

def processCommand : FrontendM Bool := do
updateCmdPos;
cs ← getCommandState;
ps ← getParserState;
c ← read;
match Parser.parseCommand cs.env c.parserCtx ps cs.messages with
| (cmd, ps, messages) => do
  setParserState ps;
  setMessages messages;
  if Parser.isEOI cmd || Parser.isExitCommand cmd then do
    pure true -- Done
  else do
    elabCommandAtFrontend cmd;
    pure false

partial def processCommandsAux : Unit → FrontendM Unit
| () => do
  done ← processCommand;
  if done then pure ()
  else processCommandsAux ()

def processCommands : FrontendM Unit :=
processCommandsAux ()

end Frontend

open Frontend

def IO.processCommands (parserCtx : Parser.ParserContextCore) (parserStateRef : IO.Ref Parser.ModuleParserState) (cmdStateRef : IO.Ref Command.State) : IO Unit := do
ps ← parserStateRef.get;
cmdPosRef ← IO.mkRef ps.pos;
EIO.adaptExcept (fun (ex : Empty) => Empty.rec _ ex) $
  processCommands { commandStateRef := cmdStateRef, parserStateRef := parserStateRef, cmdPosRef := cmdPosRef, parserCtx := parserCtx }

def process (input : String) (env : Environment) (opts : Options) (fileName : Option String := none) : IO (Environment × MessageLog) := do
let fileName   := fileName.getD "<input>";
let parserCtx  := Parser.mkParserContextCore env input fileName;
parserStateRef ← IO.mkRef { Parser.ModuleParserState . };
cmdStateRef    ← IO.mkRef $ Command.mkState env {} opts;
IO.processCommands parserCtx parserStateRef cmdStateRef;
cmdState ← cmdStateRef.get;
pure (cmdState.env, cmdState.messages)

def runFrontend (env : Environment) (input : String) (opts : Options := {}) (fileName : Option String := none) : IO (Environment × MessageLog) := do
let fileName := fileName.getD "<input>";
let parserCtx := Parser.mkParserContextCore env input fileName;
match Parser.parseHeader env parserCtx with
| (header, parserState, messages) => do
  (env, messages) ← processHeader header messages parserCtx;
  parserStateRef ← IO.mkRef parserState;
  cmdStateRef    ← IO.mkRef $ Command.mkState env messages opts;
  IO.processCommands parserCtx parserStateRef cmdStateRef;
  cmdState ← cmdStateRef.get;
  pure (cmdState.env, cmdState.messages)

@[export lean_run_frontend]
def runFrontentExport (env : Environment) (input : String) (fileName : String) (opts : Options) : IO (Option Environment) := do
(env, messages) ← runFrontend env input opts (some fileName);
messages.forM $ fun msg => IO.println msg;
if messages.hasErrors then
  pure none
else
  pure (some env)

end Elab
end Lean
