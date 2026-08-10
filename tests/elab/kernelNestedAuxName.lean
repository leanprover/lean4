import Lean.CoreM
import Lean.AddDecl

/-!
The kernel must reject declarations that name the auxiliary types the elimination of nested
inductives creates.

They were once declared in a temporary kernel environment, so a constructor naming one was checked
against a type it would not keep. The elimination now runs in Lean, against a scratch environment
that is discarded, and no such constant is ever in scope: what refuses these is ordinary type
checking, so the kernel needs no rule of its own about the name.
-/

open Lean

/--
error: (kernel) unknown constant '_nested.KNHost_1'
-/
#guard_msgs in
#eval addDecl <| .inductDecl [] 0 [
  { name := `KNAux
    type := .sort .zero
    ctors := [{ name := `KNAux.mk
                type := .forallE `x
                  (.app (.const `_nested.KNHost_1 [.zero]) (.const ``True []))
                  (.const `KNAux []) .default }] }] false

-- A `proj` names its structure type rather than mentioning it as a constant, so it reaches the
-- auxiliary type by another route; the projection is refused for the same reason.
/--
error: (kernel) invalid projection
  x.1
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
