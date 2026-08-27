module
import all Init.Prelude

/-!
# Pretty printing imported private names
https://github.com/leanprover/lean4/issues/10771
https://github.com/leanprover/lean4/issues/10772
https://github.com/leanprover/lean4/issues/10773
-/

/-!
This used to print `Lean.eraseMacroScopesAux✝ = Lean.eraseMacroScopesAux✝¹`.
-/
/-- info: Lean.eraseMacroScopesAux = Lean.eraseMacroScopesAux : Prop -/
#guard_msgs in
#check Lean.eraseMacroScopesAux = Lean.eraseMacroScopesAux

/-!
The first used to print `Lean.eraseMacroScopesAux✝`
-/
section
open Lean Name
/-- info: eraseMacroScopesAux : Name → Name -/
#guard_msgs in #check (eraseMacroScopesAux)
/-- info: eraseMacroScopes : Name → Name -/
#guard_msgs in #check (eraseMacroScopes)
end

/-!
This used to suggest `simp only [_private.Init.Prelude.0.Lean.eraseMacroScopesAux]`.
-/
/--
info: Try this:
  [apply] simp only [Lean.eraseMacroScopesAux]
-/
#guard_msgs in
example : Lean.eraseMacroScopesAux .anonymous = .anonymous := by
  simp? [Lean.eraseMacroScopesAux]

/-!
Fixing these issues involved rewriting how name unresolution handled macro scopes.
Here's a test that hygienic names can be unresolved too.
-/
macro "mk_struct" n:ident : command => `(
  structure S where
  def $n : S := {})
namespace NS
mk_struct T
/-- info: T : S✝ -/
#guard_msgs in #check (T)
end NS
/-- info: NS.T : NS.S✝ -/
#guard_msgs in #check (NS.T)
