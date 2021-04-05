def Unit.longName (f : Unit) : String := ""

inductive Cmd
  | init
    (name    : String)
    (subCmds : Array Cmd)
    (flags   : Array Unit)

open Inhabited in
instance : Inhabited Cmd where
  default := Cmd.init default default default

namespace Cmd
  def name    : Cmd → String        | init v _ _ => v
  def subCmds : Cmd → Array Cmd     | init _ v _ => v
  def flags   : Cmd → Array Unit    | init _ _ v => v

  def subCmd? (c : Cmd) (name : String)     : Option Cmd  := c.subCmds.find? (·.name = name)
  def flag?   (c : Cmd) (longName : String) : Option Unit := c.flags.find? (·.longName = longName)
  def hasFlag (c : Cmd) (longName : String) : Bool := c.flag? longName |>.isSome

  def subCmdByFullName? (c : Cmd) (fullName : Array String) : Option Cmd := OptionM.run do
    let mut c := c
    guard <| c.name = fullName.get? 0
    for subName in fullName[1:] do
      c ← c.subCmd? subName
    return c
end Cmd

structure Flag.Parsed where
  longName : String

abbrev FullCmdName := Array String

structure Cmd.Parsed where
  name  : FullCmdName
  flags : Array Flag.Parsed

namespace Cmd.Parsed
  def hasFlag (c : Cmd.Parsed) (longName : String) : Bool := false
end Cmd.Parsed

def readSubCmds : Id FullCmdName := panic! ""

def readArgs : Id (Array Flag.Parsed) := panic! ""

def parse (c : Cmd) : Id Cmd.Parsed := do
  let cmdName ← readSubCmds
  let flags ← readArgs
  let cmd := c.subCmdByFullName? cmdName |>.get!
  let defaultedFlags : Array Flag.Parsed := #[]
  -- If we uncomment /-: Cmd.Parsed -/ two lines below or comment the line below, the elaborator stops hanging.
  let flags := defaultedFlags
  let parsedCmd /- : Cmd.Parsed -/ := {
    name           := cmdName,
    flags          := flags
  }
  -- If we remove `∨ cmd.hasFlag "version" ∧ parsedCmd.hasFlag "version"` from the condition below,
  -- the timeout turns into an error. If we also remove `∧ parsedCmd.hasFlag "help"`, it works fine.
  -- Error:
  -- synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  -- instDecidableAnd
  -- inferred
  -- ?m.4652 flags✝ positionalArgs variableArgs
  if cmd.hasFlag "help" ∧ parsedCmd.hasFlag "help" ∨ cmd.hasFlag "version" ∧ parsedCmd.hasFlag "version" then
    return parsedCmd
  return parsedCmd
