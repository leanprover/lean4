import Lean.CoreM
import Lean.AddDecl

/-!
The kernel must reject declarations that name its `_nested` auxiliary types.

Those types exist only in the temporary environment used to eliminate nested
inductives. A constructor referring to one is checked there, but `restore_nested`
then rewrites the name back to the nested type, which can have a different
universe, leaving a stored constructor type that is ill typed.
-/

open Lean

/--
error: (kernel) invalid declaration 'KNAux.mk', it uses the reserved prefix '_nested'
-/
#guard_msgs in
#eval addDecl <| .inductDecl [] 0 [
  { name := `KNAux
    type := .sort .zero
    ctors := [{ name := `KNAux.mk
                type := .forallE `x
                  (.app (.const `_nested.KNHost_1 [.zero]) (.const ``True []))
                  (.const `KNAux []) .default }] }] false

-- A `proj` names its structure type, and the kernel rewrites nested occurrences in the
-- constructor to the auxiliary type, so this reaches that type without naming it as a constant.
/--
error: (kernel) invalid declaration 'KNProj.mk', it uses the reserved prefix '_nested'
-/
#guard_msgs in
#eval addDecl <| .inductDecl [] 0 [
  { name := `KNProj
    type := .sort .zero
    ctors := [{ name := `KNProj.mk
                type := .forallE `x (.const ``Nat [])
                  (.forallE `y (.proj `_nested.KNHost_1 0 (.bvar 0))
                    (.const `KNProj []) .default)
                  .default }] }] false
