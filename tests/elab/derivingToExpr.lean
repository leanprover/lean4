import Lean.Elab.Deriving.ToExpr

/-!
# Tests for the `ToExpr` deriving handler
-/

open Lean

/-!
Test without universes
-/
inductive MonoOption' (α : Type) : Type
  | some (a : α)
  | none
  deriving ToExpr

/--
info: Lean.Expr.app
  (Lean.Expr.app (Lean.Expr.const `MonoOption'.some []) (Lean.Expr.const `Bool []))
  (Lean.Expr.const `Bool.true [])
-/
#guard_msgs in
#eval repr <| toExpr <| MonoOption'.some true

/-!
Test with a universe polymorphic type parameter
-/
inductive Option' (α : Type u)
  | some (a : α)
  | none
  deriving ToExpr

/--
info: Lean.Expr.app
  (Lean.Expr.app (Lean.Expr.const `Option'.some [Lean.Level.zero]) (Lean.Expr.const `Bool []))
  (Lean.Expr.const `Bool.true [])
-/
#guard_msgs in
#eval repr <| toExpr <| Option'.some true

example : ToExpr (Option' Nat) := inferInstance

/-!
Test with higher universe levels
-/
structure MyULift.{r, s} (α : Type s) : Type (max s r) where
  up :: down : α
  deriving ToExpr

/--
info: Lean.Expr.app
  (Lean.Expr.app
    (Lean.Expr.const `Option'.some [Lean.Level.succ (Lean.Level.succ (Lean.Level.zero))])
    (Lean.Expr.app
      (Lean.Expr.const `MyULift [Lean.Level.succ (Lean.Level.succ (Lean.Level.zero)), Lean.Level.zero])
      (Lean.Expr.const `Bool [])))
  (Lean.Expr.app
    (Lean.Expr.app
      (Lean.Expr.const `MyULift.up [Lean.Level.succ (Lean.Level.succ (Lean.Level.zero)), Lean.Level.zero])
      (Lean.Expr.const `Bool []))
    (Lean.Expr.const `Bool.true []))
-/
#guard_msgs in
#eval repr <| toExpr <| Option'.some (MyULift.up.{2} true)

example : ToExpr (Option' <| MyULift.{20} Nat) := inferInstance
example [ToLevel.{u}] : ToExpr (Option' <| MyULift.{u} Nat) := inferInstance

/-!
Test with empty type.
-/
inductive Empty'
  deriving ToExpr

/-!
Test with recursive type
-/
inductive List' (α : Type u)
  | cons (a : α) (as : List' α)
  | nil
  deriving ToExpr

/-!
Test with nested type
-/
inductive Foo
  | l (x : List Foo)
  deriving ToExpr

/-!
Test with mutual inductive type
-/
mutual
inductive A
  | nil
  | cons (a : A) (b : B)
  deriving ToExpr
inductive B
  | cons₁ (a : A)
  | cons₂ (a : A) (b : B)
  deriving ToExpr
end

/--
info: Lean.Expr.app
  (Lean.Expr.app (Lean.Expr.const `A.cons []) (Lean.Expr.const `A.nil []))
  (Lean.Expr.app (Lean.Expr.const `B.cons₁ []) (Lean.Expr.const `A.nil []))
-/
#guard_msgs in
#eval repr <| toExpr <| A.cons A.nil (B.cons₁ A.nil)
/--
info: Lean.Expr.app
  (Lean.Expr.app (Lean.Expr.const `B.cons₂ []) (Lean.Expr.const `A.nil []))
  (Lean.Expr.app (Lean.Expr.const `B.cons₁ []) (Lean.Expr.const `A.nil []))
-/
#guard_msgs in
#eval repr <| toExpr <| B.cons₂ A.nil (B.cons₁ A.nil)

/-!
Test with explicit universe level
-/

inductive WithUniverse.{u} (α : Type u)
  | foo (a : α)
  deriving ToExpr

/-!
Test with universe level coming from `universe` command
-/
universe u in
inductive WithAmbientUniverse (α : Type u)
  | foo (a : α)
  deriving ToExpr

/-!
Test with an ambient universe `u`, a directly specified universe `v`, and an implicit universe `w`.
-/
universe u in
structure WithAmbientUniverseTriple.{v} (α : Type u) (β : Type v) (γ : Type w) where
  a : α
  b : β
  c : γ
  deriving ToExpr

/-!
Test using the `variable` command, with an autoimplicit universe.
-/
variable (α : Type u) in
inductive VariableParameter : Type u
  | foo (a : α)
  deriving ToExpr

/-!
Mutual inductive with universe levels.
-/
mutual
inductive A' (α : Type u) where
  | mk (x : α) (a : A' α) (b : B' α)
  deriving ToExpr
inductive B' (α : Type u) where
  | mk (x : α) (a : A' α) (b : B' α)
  deriving ToExpr
end

/-!
Nested with universe level.
-/
inductive Foo' (α : Type u)
  | l (x : α) (x : List (Foo' α))
  deriving ToExpr

/-!
### Tests with without universe autoimplicits.
-/
section NoAutoImplicit
set_option autoImplicit false

/-!
Test with universe specified directly on the type
-/
inductive ExplicitList'.{u} (α : Type u)
  | cons (a : α) (as : List' α)
  | nil
  deriving ToExpr

/-!
Test with ambient (explicit) universe
-/
universe u in
inductive AmbientList' (α : Type u)
  | cons (a : α) (as : List' α)
  | nil
  deriving ToExpr

/-!
Test with both ambient and directly specified universes.
-/
universe u in
structure ExplicitAmbientPair.{v} (α : Type u) (β : Type v) where
  a : α
  b : β
  deriving ToExpr

end NoAutoImplicit
