/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Simp.SimpM
import Lean.Meta.Sym.AlphaShareBuilder
import Lean.Meta.Sym.Simp.Result
namespace Lean.Meta.Sym.Simp

/--
Given `xs` containing free variables
`(x₁ : α₁) (x₂ : α₂[x₁]) ... (xₙ : αₙ[x₁, ..., x_{n-1}])`,
creates the custom forall congruence theorem
```
∀ (p q : (x₁ : α₁) → (x₂ : α₂[x₁]) → ... → (xₙ : αₙ[x₁, ..., x_{n-1}]) → Prop)
  (h : ∀ x₁ ... xₙ, p x₁ ... xₙ = q x₁ ... xₙ),
  (∀ x₁ ... xₙ, p x₁ ... xₙ) = (∀ x₁ ... xₙ, q x₁ ... xₙ)
```
The theorem has three arguments `p`, `q`, and `h`.
This auxiliary theorem is used by the simplifier when visiting forall expressions.
The proof uses the approach used in `mkFunextFor` followed by an `Eq.ndrec`.
-/
def mkForallCongrFor (xs : Array Expr) : MetaM Expr := do
  let prop := mkSort 0
  let type ← mkForallFVars xs prop
  let w ← Meta.getLevel type
  withLocalDeclD `p type fun p =>
  withLocalDeclD `q type fun q => do
  let eq := mkApp3 (mkConst ``Eq [1]) prop (mkAppN p xs) (mkAppN q xs)
  withLocalDeclD `h (← mkForallFVars xs eq) fun h => do
  let eqv ← mkLambdaFVars #[p, q] (← mkForallFVars xs eq)
  let quotEqv := mkApp2 (mkConst ``Quot [w]) type eqv
  withLocalDeclD `p' quotEqv fun p' => do
  let lift := mkApp6 (mkConst ``Quot.lift [w, 1]) type eqv prop
    (mkLambda `p .default type (mkAppN (.bvar 0) xs))
    (mkLambda `p .default type (mkLambda `q .default type (mkLambda `h .default (mkApp2 eqv (.bvar 1) (.bvar 0)) (mkAppN (.bvar 0) xs))))
    p'
  let extfunAppVal ← mkLambdaFVars (#[p'] ++ xs) lift
  let extfunApp := extfunAppVal
  let quotSound := mkApp5 (mkConst ``Quot.sound [w]) type eqv p q h
  let Quot_mk_p := mkApp3 (mkConst ``Quot.mk [w]) type eqv p
  let Quot_mk_q := mkApp3 (mkConst ``Quot.mk [w]) type eqv q
  let p_eq_q := mkApp6 (mkConst ``congrArg [w, w]) quotEqv type Quot_mk_p Quot_mk_q extfunApp quotSound
  let lhs ← mkForallFVars xs (mkAppN p xs)
  let rhs ← mkForallFVars xs (mkAppN q xs)
  let motive ← mkLambdaFVars #[q] (mkApp3 (mkConst ``Eq [1]) prop lhs rhs)
  let rfl := mkApp2 (mkConst ``Eq.refl [1]) prop lhs
  let result := mkApp6 (mkConst ``Eq.ndrec [0, w]) type p motive rfl q p_eq_q
  let result ← mkLambdaFVars #[p, q, h] result
  return result

open Internal

structure ArrowInfo where
  binderName : Name
  binderInfo : BinderInfo
  u          : Level
  v          : Level

structure ToArrowResult where
  arrow : Expr
  infos : List ArrowInfo
  v     : Level

def toArrow (e : Expr) : SymM ToArrowResult := do
  if let .forallE n α β bi := e then
    if !β.hasLooseBVars then
      let { arrow, infos, v } ← toArrow β
      let u ← getLevel α
      let arrow ← mkAppS₂ (← mkConstS ``Arrow [u, v]) α arrow
      let info := { binderName := n, binderInfo := bi, u, v }
      return { arrow, v := mkLevelIMax' u v, infos := info :: infos }
  return { arrow := e, infos := [], v := (← getLevel e) }

def toForall (e : Expr) (infos : List ArrowInfo) : SymM Expr := do
  let { binderName, binderInfo, .. } :: infos := infos | return e
  let_expr Arrow α β := e | return e
  mkForallS binderName binderInfo α (← toForall β infos)

/--
Recursively simplifies an `Arrow` telescope, applying telescope-specific simplifications:

- **False hypothesis**: `False → q` simplifies to `True` (via `false_arrow`)
- **True hypothesis**: `True → q` simplifies to `q` (via `true_arrow`)
- **True conclusion**: `p → True` simplifies to `True` (via `arrow_true`)

The first two are applicable only if  `q` is in `Prop` (checked via `info.v.isZero`).

Returns the simplified result paired with the remaining `ArrowInfo` list. When a telescope
collapses (e.g., to `True`), the returned `infos` list is empty, signaling to `toForall`
that no reconstruction is needed.
-/
partial def simpArrows (e : Expr) (infos : List ArrowInfo) (simpBody : Simproc) : SimpM (Result × List ArrowInfo) := do
  match infos with
  | [] => return ((← simpBody e), [])
  | info :: infos' =>
    let_expr f@Arrow p q := e | return ((← simpBody e), infos)
    let p_r ← simp p
    if (← isFalseExpr (p_r.getResultExpr p)) && info.v.isZero then
      match p_r with
      | .rfl _ => return (.step (← getTrueExpr) (mkApp (mkConst ``false_arrow) q), [])
      | .step _ h _ => return (.step (← getTrueExpr) (mkApp3 (mkConst ``false_arrow_congr) p q h), [])
    let (q_r, infos') ← simpArrows q infos' simpBody
    if (← isTrueExpr (q_r.getResultExpr q)) then
      match q_r with
      | .rfl _ => return (.step (← getTrueExpr) (mkApp (mkConst ``arrow_true [info.u]) p), [])
      | .step _ h _ => return (.step (← getTrueExpr) (mkApp3 (mkConst ``arrow_true_congr [info.u]) p q h), [])
    match p_r, q_r with
    | .rfl _, .rfl _ =>
      if (← isTrueExpr p) && info.v.isZero then
        return (.step q (mkApp (mkConst ``true_arrow) q), infos')
      else
        return (.rfl, infos)
    | .step p' h _, .rfl _ =>
      if (← isTrueExpr p') && info.v.isZero then
        return (.step q (mkApp3 (mkConst ``true_arrow_congr_left) p q h), infos')
      else
        let e' ← mkAppS₂ f p' q
        return (.step e' <| mkApp4 (mkConst ``arrow_congr_left f.constLevels!) p p' q h, info :: infos')
    | .rfl _, .step q' h _ =>
      if (← isTrueExpr p) && info.v.isZero then
        return (.step q' (mkApp3 (mkConst ``true_arrow_congr_right) q q' h), infos')
      else
        let e' ← mkAppS₂ f p q'
        return (.step e' <| mkApp4 (mkConst ``arrow_congr_right f.constLevels!) p q q' h, info :: infos')
    | .step p' h₁ _, .step q' h₂ _ =>
      if (← isTrueExpr p') && info.v.isZero then
        return (.step q' (mkApp5 (mkConst ``true_arrow_congr) p q q' h₁ h₂), infos')
      else
        let e' ← mkAppS₂ f p' q'
        return (.step e' <| mkApp6 (mkConst ``arrow_congr f.constLevels!) p p' q q' h₁ h₂, info :: infos')

/--
Simplifies a telescope of non-dependent arrows `p₁ → p₂ → ... → pₙ → q` by:
1. Converting to `Arrow p₁ (Arrow p₂ (... (Arrow pₙ q)))` (see `toArrow`)
2. Simplifying each `pᵢ` and `q` (see `simpArrows`)
3. Converting back to `→` form (see `toForall`)

Using `Arrow` (a definitional wrapper around `→`) avoids the quadratic proof growth that
occurs with `Expr.forallE`. With `forallE`, each nesting level bumps de Bruijn indices in
subterms, destroying sharing. For example, if each `pᵢ` contains a free variable `x`, the
de Bruijn representation of `x` differs at each depth, preventing hash-consing from
recognizing them as identical.

With `Arrow`, both arguments are explicit (not under binders), so subterms remain identical
across nesting levels and can be shared, yielding linear-sized proofs.

**Tradeoff**: This function simplifies each `pᵢ` and `q` individually, but misses
simplifications that depend on the arrow structure itself. For example, `q → p → p`
won't be simplified to `True` (when `p : Prop`) because the simplifier does not have
a chance to apply `post` methods to the intermediate arrow `p → p`.

Thus, this is a simproc that is meant to be used as a pre-method and marks the
result as fully simplified to prevent `simpArrow` from being applied.
-/
public def simpArrowTelescope (simpBody : Simproc := simp) : Simproc := fun e => do
  unless e.isArrow do return .rfl -- not applicable
  let { arrow, infos, v } ← toArrow e
  let (.step arrow' h _, infos) ← simpArrows arrow infos simpBody | return .rfl (done := true)
  let e' ← toForall arrow' infos
  let α := mkSort v
  let v1 := v.succ
  let h := mkApp6 (mkConst ``Eq.trans [v1]) α e arrow arrow' (mkApp2 (mkConst ``Eq.refl [v1]) α arrow) h
  let h := mkApp6 (mkConst ``Eq.trans [v1]) α e arrow' e' h (mkApp2 (mkConst ``Eq.refl [v1]) α e')
  return .step e' h (done := true)

public def simpArrow (e : Expr) : SimpM Result := do
  let p := e.bindingDomain!
  let q := e.bindingBody!
  match (← simp p), (← simp q) with
  | .rfl _, .rfl _ =>
    return .rfl
  | .step p' h _, .rfl _ =>
    let u ← getLevel p
    let v ← getLevel q
    let e' ← e.updateForallS! p' q
    return .step e' <| mkApp4 (mkConst ``implies_congr_left [u, v]) p p' q h
  | .rfl _, .step q' h _ =>
    let u ← getLevel p
    let v ← getLevel q
    let e' ← e.updateForallS! p q'
    return .step e' <| mkApp4 (mkConst ``implies_congr_right [u, v]) p q q' h
  | .step p' h₁ _, .step q' h₂ _ =>
    let u ← getLevel p
    let v ← getLevel q
    let e' ← e.updateForallS! p' q'
    return .step e' <| mkApp6 (mkConst ``implies_congr [u, v]) p p' q q' h₁ h₂

public def simpForall' (simpArrow : Simproc) (simpBody : Simproc) (e : Expr) : SimpM Result := do
  if e.isArrow then
    simpArrow e
  else if (← isProp e) then
    let n := getForallTelescopeSize e.bindingBody! 1
    forallBoundedTelescope e n fun xs b => withoutModifyingCacheIfNotWellBehaved do
      main xs (← shareCommon b)
  else
    return .rfl
where
  main (xs : Array Expr) (b : Expr) : SimpM Result := do
    match (← simpBody b) with
    | .rfl _ => return .rfl
    | .step b' h _ =>
      let h ← mkLambdaFVars xs h
      let e' ← shareCommon (← mkForallFVars xs b')
      -- **Note**: consider caching the forall-congr theorems
      let hcongr ← mkForallCongrFor xs
      return .step e' (mkApp3 hcongr (← mkLambdaFVars xs b) (← mkLambdaFVars xs b') h)

  -- **Note**: Optimize if this is quadratic in practice
  getForallTelescopeSize (e : Expr) (n : Nat) : Nat :=
    match e with
    | .forallE _ _ b _ => if b.hasLooseBVar 0 then getForallTelescopeSize b (n+1) else n
    | _ => n

public def simpForall : Simproc :=
  simpForall' simpArrow simp

end Lean.Meta.Sym.Simp
