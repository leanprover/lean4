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
