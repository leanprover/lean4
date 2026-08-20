import Lean.CoreM
import Lean.AddDecl

/-!
The kernel must reject a mutual definition whose members disagree on their
universe level parameters.

`add_mutual` shares one `type_checker` across all members, and the infer-type
cache is keyed on the expression alone, not on the level parameters in scope.
So the member declaring `u` must be checked first: it populates the cache for
`Sort u → Sort u`, and without this check the second member would hit that
entry and never run `check_level`, entering the environment with an undeclared
universe parameter in its type.
-/

open Lean

private def ty : Expr := .forallE `x (.sort (.param `u)) (.sort (.param `u)) .default
private def val : Expr := .lam `x (.sort (.param `u)) (.bvar 0) .default

/--
error: (kernel) invalid mutual definition, declarations must have the same universe level parameters
-/
#guard_msgs in
#eval addDecl <| .mutualDefnDecl [
  { name := `mutA, levelParams := [`u], type := ty, value := val,
    hints := .opaque, safety := .partial },
  { name := `mutB, levelParams := [], type := ty, value := val,
    hints := .opaque, safety := .partial }]
