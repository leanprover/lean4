import Lean.Elab.Deriving.ToExpr

open Lean

deriving instance ToExpr for ULift

-- Test with a universe polymporphic type parameter
inductive Option' (α : Type u)
  | some (a : α)
  | none
  deriving ToExpr

/-- info: instToExprOption'OfToLevel -/
#guard_msgs in #synth ToExpr (Option' Nat)
/-- info: instToExprOption'OfToLevel -/
#guard_msgs in #synth ToExpr (Option' <| ULift.{20} Nat)

/--
info: Lean.Expr.app
  (Lean.Expr.app
    (Lean.Expr.const `Option'.some [Lean.Level.succ (Lean.Level.succ (Lean.Level.succ (Lean.Level.zero)))])
    (Lean.Expr.app
      (Lean.Expr.const `ULift [Lean.Level.succ (Lean.Level.succ (Lean.Level.succ (Lean.Level.zero))), Lean.Level.zero])
      (Lean.Expr.const `Nat [])))
  (Lean.Expr.app
    (Lean.Expr.app
      (Lean.Expr.const
        `ULift.up
        [Lean.Level.succ (Lean.Level.succ (Lean.Level.succ (Lean.Level.zero))), Lean.Level.zero])
      (Lean.Expr.const `Nat []))
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
        (Lean.Expr.lit (Lean.Literal.natVal 42)))
      (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 42)))))
-/
#guard_msgs in #eval toExpr (Option'.some <| ULift.up.{3} 42)

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
