/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.EvalTerm
import Lean.Elab.ElabRules

/-!
Syntax for elaboration time control flow.
-/

namespace Lake.DSL
open Lean Elab Command

/--
The `do` command syntax groups multiple similarly indented commands together.
The group can then be passed to another command that usually only accepts a
single command (e.g., `meta if`).
-/
syntax cmdDo := ("do" many1Indent(command)) <|> command

def expandCmdDo : TSyntax ``cmdDo → Array Command
| `(cmdDo|do $cmds*) => cmds
| `(cmdDo|$cmd:command) => #[cmd]
| _ => #[]

/--
The `meta if` command has two forms:

```lean
meta if <c:term> then <a:command>
meta if <c:term> then <a:command> else <b:command>
```

It expands to the command `a` if the term `c` evaluates to true
(at elaboration time). Otherwise, it expands to command `b` (if an `else`
clause is provided).

One can use this command to specify, for example, external library targets
only available on specific platforms:

```lean
meta if System.Platform.isWindows then
extern_lib winOnlyLib := ...
else meta if System.Platform.isOSX then
extern_lib macOnlyLib := ...
else
extern_lib linuxOnlyLib := ...
```
-/
scoped syntax (name := metaIf)
"meta " "if " term " then " cmdDo (" else " cmdDo)? : command

elab_rules : command | `(meta if $c then $t $[else $e?]?) => do
  if (← withRef c <| runTermElabM fun _ => evalTerm Bool c) then
    let cmd := mkNullNode (expandCmdDo t)
    withMacroExpansion (← getRef) cmd <| elabCommand cmd
  else if let some e := e? then
    let cmd := mkNullNode (expandCmdDo e)
    withMacroExpansion (← getRef) cmd <| elabCommand cmd
