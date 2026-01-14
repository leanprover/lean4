/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.SymM
import Lean.Meta.Sym.ReplaceS
import Lean.Meta.Sym.LooseBVarsS
import Init.Grind
namespace Lean.Meta.Sym
open Internal
/--
Similar to `Lean.Expr.instantiateRevRange`.
It assumes the input is maximally shared, and ensures the output is too.
It assumes `beginIdx ≤ endIdx` and `endIdx ≤ subst.size`
-/
public def instantiateRevRangeS (e : Expr) (beginIdx endIdx : Nat) (subst : Array Expr) : SymM Expr :=
  if _ : beginIdx > endIdx then unreachable! else
  if _ : endIdx > subst.size then unreachable! else
  let s := beginIdx
  let n := endIdx - beginIdx
  replaceS e fun e offset => do
    let s₁ := s + offset
    match e with
    | .bvar idx =>
      if _h : idx >= s₁ then
        if _h : idx < offset + n then
          let v := subst[n - (idx - offset) - 1]
          liftLooseBVarsS' v 0 offset
        else
          mkBVarS (idx - n)
      else
        return some e
    | .lit _ | .mvar _ | .fvar _ | .const _ _ | .sort _ =>
      return some e
    | _ =>
      if s₁ >= e.looseBVarRange then
        return some e
      else
        return none

/--
Similar to `Lean.Expr.instantiateRev`.
It assumes the input is maximally shared, and ensures the output is too.
-/
@[inline] public def instantiateRevS (e : Expr) (subst : Array Expr) : SymM Expr :=
  instantiateRevRangeS e 0 subst.size subst

/--
Similar to `Lean.Expr.instantiateRange`.
It assumes the input is maximally shared, and ensures the output is too.
It assumes `beginIdx ≤ endIdx` and `endIdx ≤ subst.size`
-/
def instantiateRangeS' (e : Expr) (beginIdx endIdx : Nat) (subst : Array Expr) : AlphaShareBuilderM Expr :=
  if _ : beginIdx > endIdx then unreachable! else
  if _ : endIdx > subst.size then unreachable! else
  let s := beginIdx
  let n := endIdx - beginIdx
  replaceS' e fun e offset => do
    let s₁ := s + offset
    match e with
    | .bvar idx =>
      if _h : idx >= s₁ then
        if _h : idx < s₁ + n then
          let v := subst[idx - s₁]
          liftLooseBVarsS' v 0 offset
        else
          mkBVarS (idx - n)
      else
        return some e
    | .lit _ | .mvar _ | .fvar _ | .const _ _ | .sort _ =>
      return some e
    | _ =>
      if s₁ >= e.looseBVarRange then
        return some e
      else
        return none

/-- Internal variant of `instantiateS` that runs in `AlphaShareBuilderM`. -/
def instantiateS' (e : Expr) (subst : Array Expr) : AlphaShareBuilderM Expr :=
  instantiateRangeS' e 0 subst.size subst

/--
Similar to `Lean.Expr.instantiate`.
It assumes the input is maximally shared, and ensures the output is too.
-/
public def instantiateS  (e : Expr) (subst : Array Expr) : SymM Expr :=
  liftBuilderM <| instantiateS' e subst

/-- `mkAppRevRangeS f b e args == mkAppRev f (revArgs.extract b e)` -/
def mkAppRevRangeS (f : Expr) (beginIdx endIdx : Nat) (revArgs : Array Expr) : AlphaShareBuilderM Expr :=
  loop revArgs beginIdx f endIdx
where
  loop (revArgs : Array Expr) (start : Nat) (b : Expr) (i : Nat) : AlphaShareBuilderM Expr := do
  if i ≤ start then
    return b
  else
    let i := i - 1
    loop revArgs start (← mkAppS b revArgs[i]!) i

/--
Beta-reduces `f` applied to reversed arguments `revArgs`, ensuring maximally shared terms.
`betaRevS f #[a₃, a₂, a₁]` computes the beta-normal form of `f a₁ a₂ a₃`.
-/
partial def betaRevS (f : Expr) (revArgs : Array Expr) : AlphaShareBuilderM Expr :=
  if revArgs.size == 0 then
    return f
  else
    let sz := revArgs.size
    let rec go (e : Expr) (i : Nat) : AlphaShareBuilderM Expr := do
      match e with
      | .lam _ _ b _ =>
        if i + 1 < sz then
          go b (i+1)
        else
          instantiateS' b revArgs
      | .mdata _ b => go b i
      | _ =>
        let n := sz - i
        mkAppRevRangeS (← instantiateRangeS' e n sz revArgs) 0 n revArgs
    go f 0

/-- Monad for `instantiateRevBetaS'` with caching keyed by `(expression pointer, binder offset)`. -/
abbrev M := StateT (Std.HashMap (ExprPtr × Nat) Expr) AlphaShareBuilderM

/-- Caches the result `r` for `key` and returns `r`. -/
def save (key : ExprPtr × Nat) (r : Expr) : M Expr := do
  modify fun cache => cache.insert key r
  return r

/-- Internal variant of `instantiateRevBetaS` that runs in `AlphaShareBuilderM`. -/
partial def instantiateRevBetaS' (e : Expr) (subst : Array Expr) : AlphaShareBuilderM Expr := do
  if subst.isEmpty || !e.hasLooseBVars then return e
  visit e 0 |>.run' {}
where
  visitBVar (e : Expr) (bidx : Nat) (offset : Nat) : M Expr := do
    let n := subst.size
    if _h : bidx >= offset then
      if _h : bidx < offset + n then
        let v := subst[n - (bidx - offset) - 1]
        liftLooseBVarsS' v 0 offset
      else
        mkBVarS (bidx - n)
    else
      return e

  visitChild (e : Expr) (offset : Nat) : M Expr := do
    if offset >= e.looseBVarRange then
      return e
    else
      let key := (⟨e⟩, offset)
      if let some r := (← get)[key]? then
        return r
      else match e with
        | .bvar bidx => save key (← visitBVar e bidx offset)
        | .lit _ | .mvar _ | .fvar _ | .const _ _ | .sort _ => save key e
        | e => save key (← visit e offset)

  visitAppDefault (e : Expr) (offset : Nat) : M Expr := do
    match e with
    | .app f a =>
      let key := (⟨e⟩, offset)
      if let some r := (← get)[key]? then
        return r
      else
        save key (← e.updateAppS! (← visitAppDefault f offset) (← visitChild a offset))
    | e => visitChild e offset

  visitAppBeta (e : Expr) (f : Expr) (argsRev : Array Expr) (offset : Nat) (modified : Bool) : M Expr := do
    match f with
    | .app f a =>
      let a' ← visitChild a offset
      visitAppBeta e f (argsRev.push a') offset (modified || !isSameExpr a a')
    | .bvar bidx =>
      let f' ← visitBVar f bidx offset
      if modified || !isSameExpr f f' then
        betaRevS f' argsRev
      else
        return e
    | _ => unreachable!

  visitApp (e : Expr) (f : Expr) (arg : Expr) (offset : Nat) (_ : e = .app f arg) : M Expr := do
    let arg' ← visitChild arg offset
    if f.getAppFn.isBVar then
      visitAppBeta e f #[arg'] offset (!isSameExpr arg arg')
    else
      e.updateAppS! (← visitAppDefault f offset) arg'

  visit (e : Expr) (offset : Nat) : M Expr := do
    match h : e with
    | .lit _ | .mvar _ | .fvar _ | .const _ _ | .sort _ => unreachable!
    | .bvar bidx => visitBVar e bidx offset
    | .app f a => visitApp e f a offset h
    | .mdata _ a => e.updateMDataS! (← visitChild a offset)
    | .proj _ _ a => e.updateProjS! (← visitChild a offset)
    | .forallE _ d b _ => e.updateForallS! (← visitChild d offset) (← visitChild b (offset+1))
    | .lam _ d b _ => e.updateLambdaS! (← visitChild d offset) (← visitChild b (offset+1))
    | .letE _ t v b _ => e.updateLetS! (← visitChild t offset) (← visitChild v offset) (← visitChild b (offset+1))

/--
Similar to `instantiateRevS`, but beta-reduces nested applications whose function becomes a lambda
after substitution.

For example, if `e` contains a subterm `#0 a` and we apply the substitution `#0 := fun x => x + 1`,
then `instantiateRevBetaS` produces `a + 1` instead of `(fun x => x + 1) a`.

This is useful when applying theorems. For example, when applying `Exists.intro`:
```
Exists.intro.{u} {α : Sort u} {p : α → Prop} (w : α) (h : p w) : Exists p
```
to a goal of the form `∃ x : Nat, p x ∧ q x`, we create metavariables `?w` and `?h`.
With `instantiateRevBetaS`, the type of `?h` becomes `p ?w ∧ q ?w` instead of
`(fun x => p x ∧ q x) ?w`.
-/
public def instantiateRevBetaS (e : Expr) (subst : Array Expr) : SymM Expr := do
  if !e.hasLooseBVars || subst.isEmpty then return e
  else liftBuilderM <| instantiateRevBetaS' e subst

end Lean.Meta.Sym
