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
else if System.Platform.isOSX then
extern_lib macOnlyLib := ...
else
extern_lib linuxOnlyLib := ...
```
-/
scoped syntax (name := metaIf)
"meta " "if " term " then " command (" else " command)? : command

elab_rules : command | `(meta if $c then $t $[else $e?]?) => do
  if (← withRef c <| runTermElabM none <| fun _ => evalTerm Bool c) then
    withMacroExpansion (← getRef) t <| elabCommand t
  else if let some e := e? then
    withMacroExpansion (← getRef) e <| elabCommand e
