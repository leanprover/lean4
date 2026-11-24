/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util
public import Lean.Meta.IntInstTesters
public section
namespace Lean.Meta.Grind.Arith.Cutsat
/-!
`Int` expressions are normalized by the `grind` preprocessor, but we
dynamically convert expressions from other types into `Int` expressions
and these expressions must be normalized inside of the cutsat module.
-/

/-
**Note**: It is safe to use (the more efficient) structural instances tests here because `grind` uses the canonicalizer.
-/
open Structural in
@[specialize] private partial def toLinearExprAux {m : Type → Type} [Monad m] [MonadLiftT MetaM m]
    (toVar : Expr → Nat → m Int.Internal.Linear.Expr) (e : Expr) (generation : Nat) : m Int.Internal.Linear.Expr := do
  let mul (a b : Expr) := do
    match (← getIntValue? a) with
    | some k => return .mulL k (← toLinearExprAux toVar b 0)
    | none => match (← getIntValue? b) with
      | some k => return .mulR (← toLinearExprAux toVar a 0) k
      | none => toVar e generation
  let t ← if e.hasExprMVar then instantiateMVarsIfMVarApp e else pure e
  match_expr (meta := false) t with
  | OfNat.ofNat _ _ _ =>
    if let some n ← getIntValue? e then return .num n
    else toVar e generation
  | Neg.neg _ i a =>
    if (← isInstNegInt i) then return .neg (← toLinearExprAux toVar a 0)
    else toVar e generation
  | HAdd.hAdd _ _ _ i a b =>
    if (← isInstHAddInt i) then return .add (← toLinearExprAux toVar a 0) (← toLinearExprAux toVar b 0)
    else toVar e generation
  | HSub.hSub _ _ _ i a b =>
    if (← isInstHSubInt i) then return .sub (← toLinearExprAux toVar a 0) (← toLinearExprAux toVar b 0)
    else toVar e generation
  | HMul.hMul _ _ _ i a b =>
    if (← isInstHMulInt i) then mul a b
    else toVar e generation
  | _ => toVar e generation

/-- Reifies a linear integer expression using the caller's variables for opaque subterms. -/
@[inline] def toLinearExprWith {m : Type → Type} [Monad m] [MonadLiftT MetaM m]
    (toVar : Expr → m Var) (e : Expr) : m Int.Internal.Linear.Expr :=
  toLinearExprAux (fun e _ => do return .var (← toVar e)) e 0

/-- Converts the given integer expression into `Int.Internal.Linear.Expr`. -/
def toLinearExpr (e : Expr) (generation : Nat := 0) : GoalM Int.Internal.Linear.Expr :=
  let toVar (atom : Expr) (gen : Nat) : GoalM Int.Internal.Linear.Expr := do
    let atom ← shareCommon atom
    if (← alreadyInternalized atom) then
      return .var (← mkVar atom)
    else
      internalize atom gen
      return .var (← mkVar atom)
  toLinearExprAux toVar e generation

end Lean.Meta.Grind.Arith.Cutsat
