module
import all Init.Prelude

/-!
# Pretty printing imported private names
https://github.com/leanprover/lean4/issues/10771
https://github.com/leanprover/lean4/issues/10772
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
