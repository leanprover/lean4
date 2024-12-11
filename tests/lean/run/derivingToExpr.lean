import Lean.Elab.Deriving.ToExpr

open Lean (ToExpr)

-- Test with a universe polymporphic type parameter
inductive Option' (α : Type u)
  | some (a : α)
  | none
  deriving ToExpr

-- Test with recursive type
inductive List' (α : Type u)
  | cons (a : α) (as : List' α)
  | nil
  deriving ToExpr

-- Test without (universe) auto implicit
set_option autoImplicit false in
inductive ExplicitList'.{u} (α : Type u)
  | cons (a : α) (as : List' α)
  | nil
  deriving ToExpr
