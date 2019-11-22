/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import Init.System.IO
import Init.Lean.Attributes
import Init.Lean.Message
import Init.Lean.Syntax

namespace Lean

def Linter := Environment → Name → /-Syntax → -/IO MessageLog

def mkLintersRef : IO (IO.Ref (Array Linter)) :=
IO.mkRef #[]

/- Linters should be loadable as plugins, so store in a global IO ref instead of an attribute managed by the
   environment (which only contains `import`ed objects). -/
@[init mkLintersRef, export lean_linters_ref]
constant lintersRef : IO.Ref (Array Linter) := arbitrary _

def addLinter (l : Linter) : IO Unit := do
  ls ← lintersRef.get;
  lintersRef.set (ls.push l)

end Lean
