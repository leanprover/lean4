import Lean.Elab.Deriving.ToExpr

open Lean

deriving instance ToExpr for ULift

-- Test with empty type
inductive Empty'
  deriving ToExpr

-- Test without universes
inductive MonoOption' (α : Type) : Type
  | some (a : α)
  | none
  deriving ToExpr

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

inductive WithUniverse.{u} (α : Type u)
  | foo (a : α)
  deriving ToExpr

universe u in
inductive WithAmbientUniverse (α : Type u)
  | foo (a : α)
  deriving ToExpr

-- A test with: an ambient universe `u`, a directly specified universe `v`, and
-- an implicit universe `w`
universe u in
structure WithAmbientUniverseTriple.{v} (α : Type u) (β : Type v) (y : Type w) where
  a : α
  b : β
  c : γ
  deriving ToExpr

-- Tests without (universe) auto implicits
section NoAutoImplicit
set_option autoImplicit false

-- Test with universe specified directly on the type
inductive ExplicitList'.{u} (α : Type u)
  | cons (a : α) (as : List' α)
  | nil
  deriving ToExpr

-- Test with ambient (explicit) universe
universe u in
inductive AmbientList' (α : Type u)
  | cons (a : α) (as : List' α)
  | nil
  deriving ToExpr

-- Now, test both ambient and directly specified universes
universe u in
structure ExplicitAmbientPair.{v} (α : Type u) (β : Type v) where
  a : α
  b : β
  deriving ToExpr

end NoAutoImplicit
