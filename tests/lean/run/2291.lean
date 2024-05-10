import Lean.Elab.Command
import Lean.Elab.Open
/-!
Issue #2291

The following example would cause the pretty printer to panic.
-/

set_option trace.compiler.simp true in
#eval [0]


/-!
Fixing the above involved changing `Lean.unresolveNameGlobal`.
Here, we also verify that we do not pretty print using any aliases that have macro scopes.
-/

open Lean in
elab "add_bad_alias " n:ident : command => withFreshMacroScope do
  let declName ← Elab.OpenDecl.resolveNameUsingNamespaces [← getCurrNamespace] n
  let badName ← MonadQuotation.addMacroScope `bad
  modify fun s => { s with env := addAlias s.env badName declName }

def f := 1

add_bad_alias f

-- Formerly was info: bad✝ : ℕ
/-- info: f : Nat -/
#guard_msgs in #check (f)
