/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Error
public import Lean.Parser.Module.Syntax
import Lean.Parser.Module

namespace Lean.Fmt

public def headerKind := ``Parser.Module.header
public def moduleKind := ``Parser.Module.module
public def cmdsKind := `Lean.Parser.Module.cmds

public def findAbnormalTerminalCommand? (stxs : Array Syntax) : Option Syntax :=
  stxs.find? fun stx => Parser.isTerminalCommand stx && ! stx.isOfKind ``Parser.Command.eoi

/--
Builds the module syntax that the formatter operates on.

Yields `none` if `cmdStxs` contains a terminal command other than `Lean.Parser.Command.eoi`, i.e.
`#exit` or an `import` after the module header. Command parsing stops at such a command, so the
remainder of the file is missing from `cmdStxs` and formatting the result would delete it.
-/
public def mkModuleSyntax (headerStx : Syntax) (cmdStxs : Array Syntax) : Except Error Syntax := do
  if let some abnormalTerminalCommand := findAbnormalTerminalCommand? cmdStxs then
    throw <| .input <| .earlyTerminationCommand abnormalTerminalCommand
  return mkNode moduleKind #[headerStx, mkNode cmdsKind cmdStxs]
