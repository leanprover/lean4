import Lean
open Lean Meta

/-- `inductive T : Type → Type | mk : (a : Type) → (y : #1) → T #1`, with one parameter. -/
def decl : Declaration :=
  .inductDecl [] 1
    [{ name := `T, type := .forallE `a (.sort 1) (.sort 1) .default,
       ctors := [{ name := `T.mk,
                   type := .forallE `a (.sort 1)
                             (.forallE `y (.bvar 1) (.app (.const `T []) (.bvar 1)) .default) .default }] }]
    false

/--
error: (kernel) type checker does not support loose bound variables, replace them with free variables before invoking it
-/
#guard_msgs in
run_meta do addDecl decl
