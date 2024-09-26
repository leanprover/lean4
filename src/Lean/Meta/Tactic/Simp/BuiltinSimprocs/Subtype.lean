/-
Copyright (c) 2024 Lean FRO. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Lean.Meta.LitValues
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat

namespace Subtype
open Lean Meta Simp

/--
Rewrite a function `f : { x // p x } → α` in the form `f' ∘ Subtype.val` if (syntactically) possible.
-/
def asCompVal (f : Expr) : MetaM (Option Expr) := do
  let Expr.lam n d b bi := f | return none
  let_expr Subtype α p := d | return none
  let some b' := replaceValBVar 0 b | return none
  let f' := .lam n α b' bi
  let r ← mkAppM ``Function.comp #[f', ← mkAppOptM ``Subtype.val #[α, p]]
  return (some r)
where
  /--
  Walk down `e`, replacing `Subtype.val #k` with `#k`,
  and returning `none` if there are any `#k`s not in this position.
  -/
  replaceValBVar (k : Nat) (e : Expr) : Option Expr  :=
    match e with
    | .app (.app (.app (.const n _) _) _) (.bvar k') =>
      if k = k'  then
        if n = `Subtype.val then return .bvar k else none
      else
        return e
    | .bvar i => if i = k then none else return e
    | .app f x => return .app (← replaceValBVar k f) (← replaceValBVar k x)
    | .lam n d b bi => return .lam n (← replaceValBVar k d) (← replaceValBVar (k+1) b) bi
    | .forallE n d b bi => return .forallE n (← replaceValBVar k d) (← replaceValBVar (k+1) b) bi
    | .letE n t v b d => return .letE n (← replaceValBVar k t) (← replaceValBVar k v) (← replaceValBVar (k+1) b) d
    | .proj n i e => return .proj n i (← replaceValBVar k e)
    | .mdata data e => return .mdata data (← replaceValBVar k e)
    | .lit _
    | .const _ _
    | .sort _
    | .mvar _
    | .fvar _ => return e

/--
Simplify `l.map f`, where `l : List { x // p x }` and `f` factors as `f' ∘ Subtype.val`,
to `l.map (f' ∘ Subtype.val)`.
 -/
builtin_dsimproc [simp, seval] reduceMapSubtype (List.map _ _) := fun e => do
  let_expr List.map _ _ f l ← e | return .continue
  let some f' ← asCompVal f | return .continue
  return .done <| (← mkAppM ``List.map #[f', l])

end Subtype
