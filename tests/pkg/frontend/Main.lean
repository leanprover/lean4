import Lean.Elab.Frontend

open Lean Elab

unsafe def processInput (input : String) (initializers := false)  :
    IO (Environment × List Message) := do
  let fileName   := "<input>"
  let inputCtx   := Parser.mkInputContext input fileName
  if initializers then enableInitializersExecution
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header {} messages inputCtx
  let s ← IO.processCommands inputCtx parserState (Command.mkState env messages {}) <&> Frontend.State.commandState
  pure (s.env, s.messages.msgs.toList)

open System in
def findLean (mod : Name) : IO FilePath := do
  let olean ← findOLean mod
  let lean := olean.toString.replace "build/lib/" ""
  return FilePath.mk lean |>.withExtension "lean"

/-- Read the source code of the named module. -/
def moduleSource (mod : Name) : IO String := do
  IO.FS.readFile (← findLean mod)

unsafe def compileModule (mod : Name) (initializers := false) :
    IO (Environment × List Message) := do
  processInput (← moduleSource mod) initializers

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mut count : UInt32 := 0
  for mod in args do
    IO.println s!"Compiling {mod}"
    let (_env, msgs) ← compileModule mod.toName true
    for m in msgs do IO.println (← m.toString)
    if msgs.length > 0 then count := 1
  return count
