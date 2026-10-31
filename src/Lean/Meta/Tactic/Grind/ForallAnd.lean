/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Basic
import Init.Grind.Norm
import Lean.Meta.InferType
import Lean.Meta.AppBuilder
public section
namespace Lean.Meta.Grind

/--
Distributes universal quantifiers over a conjunction at the end of a binder telescope.
If `e` is `∀ x₁ … xₙ, a ∧ b`, where at least one binder is dependent (a genuine `∀`, not an
arrow), returns `(lhs, rhs, h)` with `lhs := ∀ x₁ … xₙ, a`, `rhs := ∀ x₁ … xₙ, b`, and
`h : e = (lhs ∧ rhs)`.

`∀ x, p x ∧ q x` is split so that each conjunct gets its own E-matching pattern, and the arrows
in `∀ x, p x → q x ∧ r x` must not block that. A telescope of arrows alone, `p → a ∧ b`, is
kept: `grind` propagates `a ∧ b` from `p` without a case split.
-/
partial def forallImpAnd? (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  unless isCandidate e do return none
  let some (lhs, rhs, h?, true) ← go e | return none
  let some h := h? | return none -- unreachable: `e` has at least one binder
  return some (lhs, rhs, h)
where
  /-- Syntactic probe: the telescope ends in a conjunction and some binder is dependent. -/
  isCandidate (e : Expr) : Bool :=
    e.isForall && e.getForallBody.isAppOfArity ``And 2 && hasDepBinder e
  hasDepBinder : Expr → Bool
    | .forallE _ _ b _ => b.hasLooseBVar 0 || hasDepBinder b
    | _ => false
  /--
  For `t := ∀ x₁ … xₙ, a ∧ b`, returns `(∀ x₁ … xₙ, a, ∀ x₁ … xₙ, b, h?, dep)` with
  `h? : t = (… ∧ …)`, or `none` for `n = 0` where the equation is `rfl`,
  and `dep := true` if some binder is dependent.
  -/
  go (t : Expr) : MetaM (Option (Expr × Expr × Option Expr × Bool)) := do
    match_expr t with
    | And a b => return some (a, b, none, false)
    | _ =>
      let .forallE n p rest bi := t | return none
      let u ← getLevel p
      if rest.hasLooseBVars then
        withLocalDecl n bi p fun x => do
          let rest := rest.instantiate1 x
          let some (a, b, h?, _) ← go rest | return none
          let lhs ← mkForallFVars #[x] a
          let rhs ← mkForallFVars #[x] b
          let hAnd := mkApp3 (mkConst ``Grind.forall_and [u]) p (← mkLambdaFVars #[x] a) (← mkLambdaFVars #[x] b)
          let some h := h? | return some (lhs, rhs, some hAnd, true)
          let hCongr := mkApp4 (mkConst ``forall_congr [u]) p (← mkLambdaFVars #[x] rest) (← mkLambdaFVars #[x] (mkAnd a b)) (← mkLambdaFVars #[x] h)
          return some (lhs, rhs, some (mkEqTransCoreProp t (← mkForallFVars #[x] (mkAnd a b)) (mkAnd lhs rhs) hCongr hAnd), true)
      else
        let some (a, b, h?, dep) ← go rest | return none
        let lhs := mkForall n bi p a
        let rhs := mkForall n bi p b
        let hAnd := mkApp3 (mkConst ``Grind.forall_and [u]) p (mkLambda n bi p a) (mkLambda n bi p b)
        let some h := h? | return some (lhs, rhs, some hAnd, dep)
        let hCongr := mkApp4 (mkConst ``implies_congr_right [u, 0]) p rest (mkAnd a b) h
        return some (lhs, rhs, some (mkEqTransCoreProp t (mkForall n bi p (mkAnd a b)) (mkAnd lhs rhs) hCongr hAnd), dep)

end Lean.Meta.Grind
