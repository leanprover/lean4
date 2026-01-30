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
Checks if `body` is eta-expanded with `n` applications: `f (.bvar (n-1)) ... (.bvar 0)`.
Returns `f` if so and `f` has no loose bvars; otherwise returns `default`.
- `n`: number of remaining applications to check
- `i`: expected bvar index (starts at 0, increments with each application)
- `default`: returned when not eta-reducible (enables pointer equality check)
-/
def etaReduceAux (body : Expr) (n : Nat) (i : Nat) (default : Expr) : Expr := Id.run do
  match n with
  | 0 => if body.hasLooseBVars then default else body
  | n+1 =>
    let .app f (.bvar j) := body | default
    if j == i then etaReduceAux f n (i+1) default else default

/--
If `e` is of the form `(fun x₁ ... xₙ => f x₁ ... xₙ)` and `f` does not contain `x₁`, ..., `xₙ`,
then returns `f`. Otherwise, returns `e`.

Returns the original expression when not reducible to enable pointer equality checks.
-/
public def etaReduce (e : Expr) : Expr :=
  go e 0
where
  go (body : Expr) (n : Nat) : Expr :=
    match body with
    | .lam _ _ b _ => go b (n+1)
    | _ => if n == 0 then e else etaReduceAux body n 0 e

/-- Returns `true` if `e` can be eta-reduced. Uses pointer equality for efficiency. -/
public def isEtaReducible (e : Expr) : Bool :=
  !isSameExpr e (etaReduce e)

/-- Applies `etaReduce` to all subexpressions. Returns `e` unchanged if no subexpression is eta-reducible. -/
public def etaReduceAll (e : Expr) : MetaM Expr := do
  unless Option.isSome <| e.find? isEtaReducible do return e
  let pre (e : Expr) : MetaM TransformStep := do
    let e' := etaReduce e
    if isSameExpr e e' then return .continue
    else return .visit e'
  Meta.transform e (pre := pre)

end Lean.Meta.Sym
