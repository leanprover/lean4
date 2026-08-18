/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.ExprPtr
public import Lean.Meta.Basic
import Lean.Meta.Transform
namespace Lean.Meta.Sym

/--
Returns `true` if `e` contains a loose bound variable with index in `[0, n)`
This function assumes `n` is small. If this becomes a bottleneck, we should
implement a version of `lean_expr_has_loose_bvar` that checks the range in one traversal.
-/
def hasLooseBVarsInRange (e : Expr) (n : Nat) : Bool :=
  e.hasLooseBVars && go n
where
  go : Nat → Bool
  | 0 => false
  | i+1 => e.hasLooseBVar i || go i

/--
Checks if `body` is eta-expanded with `n` applications: `f (.bvar (n-1)) ... (.bvar 0)`.
Returns `f` if so and `f` has no loose bvars with indices in the range `[0, n)`; otherwise returns `default`.
- `n`: number of remaining applications to check
- `i`: expected bvar index (starts at 0, increments with each application)
- `default`: returned when not eta-reducible (enables pointer equality check)
-/
def etaReduceAux (body : Expr) (n : Nat) (i : Nat) (default : Expr) : Expr :=
  go body n i
where
  go (body : Expr) (m : Nat) (i : Nat) : Expr := Id.run do
    match m with
    | 0 =>
      if hasLooseBVarsInRange body n then default
      else body.lowerLooseBVars n n
    | m+1 =>
      let .app f (.bvar j) := body | default
      if j == i then go f m (i+1) else default

/--
If `e` is of the form `(fun x₁ ... xₙ => f x₁ ... xₙ)` and `f` does not contain `x₁`, ..., `xₙ`,
then returns `f`. Otherwise, returns `e`.

Returns the original expression when not reducible to enable pointer equality checks.
-/
public def etaReduce (e : Expr) : Expr :=
  if e.isLambda then go e 0 else e
where
  go (body : Expr) (n : Nat) : Expr :=
    match body with
    | .lam _ _ b _ => go b (n+1)
    | _ => etaReduceAux body n 0 e

/-- Returns `true` if `e` can be eta-reduced. Uses pointer equality for efficiency. -/
public def isEtaReducible (e : Expr) : Bool :=
  !isSameExpr e (etaReduce e)

public partial def etaReduceWithCache (e : Expr) (c : Std.HashMap ExprPtr Expr) : CoreM (Expr × Std.HashMap ExprPtr Expr) := do
  visit e |>.run c
where
  cache (e e' : Expr) : StateRefT (Std.HashMap ExprPtr Expr) CoreM Expr := do
    modify fun s => s.insert { expr := e } e'
    return e'

  visit (e : Expr) : StateRefT (Std.HashMap ExprPtr Expr) CoreM Expr := withIncRecDepth do
    if let some e' := (← get).get? { expr := e } then
      return e'
    match e with
    | .forallE _ d b _ => cache e (e.updateForallE! (← visit d) (← visit b))
    | .lam _ d b _ =>
      let e' := etaReduce.go e e 0
      if isSameExpr e e' then
        cache e (e.updateLambdaE! (← visit d) (← visit b))
      else
        cache e (← visit e')
    | .letE _ t v b _  => cache e (e.updateLetE! (← visit t) (← visit v) (← visit b))
    | .app f a         => cache e (e.updateApp! (← visit f) (← visit a))
    | .mdata _ b       => cache e (e.updateMData! (← visit b))
    | .proj _ _ b      => cache e (e.updateProj! (← visit b))
    | _                => return e

/-- Applies `etaReduce` to all subexpressions. Returns `e` unchanged if no subexpression is eta-reducible. -/
public def etaReduceAll (e : Expr) : CoreM Expr := do
  unless Option.isSome <| e.find? isEtaReducible do return e
  let (e, _) ← etaReduceWithCache e {}
  return e

end Lean.Meta.Sym
