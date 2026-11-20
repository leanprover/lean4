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
import Lean.Meta.Sym.Util
import Lean.Meta.Sym.InstantiateS
import Lean.Meta.Sym.AbstractS
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
public def mkForallCongrFor (xs : Array Expr) : MetaM Expr := do
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

open Lean.Meta.Sym.Internal

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
    -- **cd propagation**: `cd` from `simp p` and `simp q` (via recursive `simpArrows`)
    -- must be propagated through ALL branches. Even when `p` is already False/True
    -- and hasn't changed, `cd = true` means `simp p` might take a different code path
    -- in another local context (e.g., a conditional rewrite could succeed), which would
    -- lead to a completely different result for the arrow expression.
    let p_r ← simp p
    if (← isFalseExpr (p_r.getResultExpr p)) && info.v.isZero then
      match p_r with
      | .rfl _ cd => return (.step (← getTrueExpr) (mkApp (mkConst ``false_arrow) q) (contextDependent := cd), [])
      | .step _ h _ cd => return (.step (← getTrueExpr) (mkApp3 (mkConst ``false_arrow_congr) p q h) (contextDependent := cd), [])
    let (q_r, infos') ← simpArrows q infos' simpBody
    if (← isTrueExpr (q_r.getResultExpr q)) then
      let cd := p_r.isContextDependent || q_r.isContextDependent
      match q_r with
      | .rfl _ _ => return (.step (← getTrueExpr) (mkApp (mkConst ``arrow_true [info.u]) p) (contextDependent := cd), [])
      | .step _ h _ _ => return (.step (← getTrueExpr) (mkApp3 (mkConst ``arrow_true_congr [info.u]) p q h) (contextDependent := cd), [])
    match p_r, q_r with
    | .rfl _ cd₁, .rfl _ cd₂ =>
      let cd := cd₁ || cd₂
      if (← isTrueExpr p) && info.v.isZero then
        return (.step q (mkApp (mkConst ``true_arrow) q) (contextDependent := cd), infos')
      else
        return (mkRflResultCD cd, infos)
    | .step p' h _ cd₁, .rfl _ cd₂ =>
      let cd := cd₁ || cd₂
      if (← isTrueExpr p') && info.v.isZero then
        return (.step q (mkApp3 (mkConst ``true_arrow_congr_left) p q h) (contextDependent := cd), infos')
      else
        let e' ← mkAppS₂ f p' q
        let proof := mkApp4 (mkConst ``arrow_congr_left f.constLevels!) p p' q h
        return (.step e' proof (contextDependent := cd), info :: infos')
    | .rfl _ cd₁, .step q' h _ cd₂ =>
      let cd := cd₁ || cd₂
      if (← isTrueExpr p) && info.v.isZero then
        return (.step q' (mkApp3 (mkConst ``true_arrow_congr_right) q q' h) (contextDependent := cd), infos')
      else
        let e' ← mkAppS₂ f p q'
        let proof := mkApp4 (mkConst ``arrow_congr_right f.constLevels!) p q q' h
        return (.step e' proof (contextDependent := cd), info :: infos')
    | .step p' h₁ _ cd₁, .step q' h₂ _ cd₂ =>
      if (← isTrueExpr p') && info.v.isZero then
        return (.step q' (mkApp5 (mkConst ``true_arrow_congr) p q q' h₁ h₂) (contextDependent := cd₁ || cd₂), infos')
      else
        let e' ← mkAppS₂ f p' q'
        let proof := mkApp6 (mkConst ``arrow_congr f.constLevels!) p p' q q' h₁ h₂
        return (.step e' proof (contextDependent := cd₁ || cd₂), info :: infos')

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
  match (← simpArrows arrow infos simpBody) with
  | (.rfl _ cd, _) => return mkRflResult (done := true) (contextDependent := cd)
  | (.step arrow' h _ cd, infos) =>
  let e' ← toForall arrow' infos
  let α := mkSort v
  let v1 := v.succ
  let h := mkApp6 (mkConst ``Eq.trans [v1]) α e arrow arrow' (mkApp2 (mkConst ``Eq.refl [v1]) α arrow) h
  let h := mkApp6 (mkConst ``Eq.trans [v1]) α e arrow' e' h (mkApp2 (mkConst ``Eq.refl [v1]) α e')
  return .step e' h (done := true) (contextDependent := cd)

public def simpArrow (e : Expr) : SimpM Result := do
  let p := e.bindingDomain!
  let q := e.bindingBody!
  -- Propagate `cd` from both domain and codomain: if either sub-simplification
  -- was context-dependent, `simp` might take a different path in another context.
  match (← simp p), (← simp q) with
  | .rfl _ cd₁, .rfl _ cd₂ =>
    return mkRflResultCD (cd₁ || cd₂)
  | .step p' h _ cd₁, .rfl _ cd₂ =>
    let u ← getLevel p
    let v ← getLevel q
    let e' ← e.updateForallS! p' q
    return .step e' (mkApp4 (mkConst ``implies_congr_left [u, v]) p p' q h) (contextDependent := cd₁ || cd₂)
  | .rfl _ cd₁, .step q' h _ cd₂ =>
    let u ← getLevel p
    let v ← getLevel q
    let e' ← e.updateForallS! p q'
    return .step e' (mkApp4 (mkConst ``implies_congr_right [u, v]) p q q' h) (contextDependent := cd₁ || cd₂)
  | .step p' h₁ _ cd₁, .step q' h₂ _ cd₂ =>
    let u ← getLevel p
    let v ← getLevel q
    let e' ← e.updateForallS! p' q'
    return .step e' (mkApp6 (mkConst ``implies_congr [u, v]) p p' q q' h₁ h₂) (contextDependent := cd₁ || cd₂)

/--
Builds the cast `h.substr a : p₁` for `h : p₁ = p₂` and `a : p₂`. It replaces the bound variable of
`∀ a : p₁, q a` (or `∃ a : p₁, q a`) when the domain is rewritten to `p₂`, see
`forall_prop_congr_dom` and `exists_prop_congr_dom`.

Remark: `h` is not a maximally shared term.
-/
def mkPropDomainCastS (p₁ p₂ h a : Expr) : SymM Expr := do
  let prop ← mkSortS 0
  let h ← shareCommon h
  mkAppS₆ (← mkConstS ``Eq.substr [1]) prop (← mkLambdaS `x .default prop (← mkBVarS 0)) p₂ p₁ h a

public partial def simpForall' (simpArrow : Simproc) (simpBody : Simproc) (e : Expr) : SimpM Result := do
  if e.isArrow then
    simpArrow e
  else if (← isProp e) then
    go #[] e false
  else
    return .rfl
where
  /--
  Collects the telescope of dependent binders whose domains are already in normal form, and
  simplifies the body with a single congruence step (`mkForallCongrFor`). The telescope stops at
  a non-dependent binder (then `simpBody` simplifies the arrow), and at a propositional domain
  that simplifies (then `simpPropDomain` rewrites it).
  `e` is open: its loose bound variables refer to `xs`. Only the domains are instantiated while
  walking the telescope; the body is instantiated once, when the telescope stops.
  `cd` accumulates the context dependency of the domains visited so far.
  -/
  go (xs : Array Expr) (e : Expr) (cd : Bool) : SimpM Result := do
    if let .forallE n d b bi := e then
      if b.hasLooseBVar 0 then
        let d ← close xs d
        let mut cd := cd
        if (← isProp d) then
          match (← under xs (simp d)) with
          | .rfl _ cd' => cd := cd || cd'
          | .step d' h _ cd' =>
            let e ← close xs e
            return (← mkCongr xs e (← simpPropDomain e d' h) (cd || cd'))
        return (← withLocalDeclS n bi d fun x => go (xs.push x) b cd)
    let b ← close xs e
    mkCongr xs b (← under xs (simpBody b)) cd

  /-- Runs `k`, which simplifies a term under the binders `xs`, with a fresh transient cache. -/
  under {α} (xs : Array Expr) (k : SimpM α) : SimpM α :=
    if xs.isEmpty then k else withFreshTransientCache k

  /-- Instantiates the loose bound variables of `e` with `xs`. -/
  close (xs : Array Expr) (e : Expr) : SimpM Expr :=
    instantiateRevS e xs

  /-- Converts the result `r` for the body `b` of the telescope `xs` into a result for `∀ xs, b`. -/
  mkCongr (xs : Array Expr) (b : Expr) (r : Result) (cd₀ : Bool) : SimpM Result := do
    -- Propagate `cd` from the body: in another context the body might simplify differently.
    match r with
    | .rfl _ cd => return mkRflResultCD (cd₀ || cd)
    | .step b' h done cd =>
      if xs.isEmpty then
        return .step b' h done (cd₀ || cd)
      let h ← mkLambdaFVars xs h
      let e' ← shareCommon (← mkForallFVars xs b')
      -- **Note**: consider caching the forall-congr theorems
      let hcongr ← mkForallCongrFor xs
      return .step e' (mkApp3 hcongr (← mkLambdaFVars xs b) (← mkLambdaFVars xs b') h) (contextDependent := cd₀ || cd)

  /--
  `e` is `∀ a : p₁, q a` with `p₁ : Prop`, and `h : p₁ = p₂` is the result of simplifying the
  domain. The bound variable is replaced by the cast `h.substr a` in the body, which is then
  simplified under `a : p₂`. The proof uses `forall_prop_congr_dom` when the body does not
  change, and `forall_prop_domain_congr` otherwise.
  -/
  simpPropDomain (e p₂ h : Expr) : SimpM Result := do
    let .forallE n p₁ body bi := e | unreachable!
    let q₁ := mkLambda n bi p₁ body
    withLocalDeclS n bi p₂ fun a => withFreshTransientCache do
      let h' ← mkPropDomainCastS p₁ p₂ h a
      let b ← instantiateS body #[h']
      match (← simpBody b) with
      | .rfl _ cd =>
        let e' ← mkForallFVarsS #[a] b
        return .step e' (mkApp4 (mkConst ``forall_prop_congr_dom) p₁ p₂ h q₁) (contextDependent := cd)
      | .step b' h₂ _ cd =>
        let h₂ ← mkLambdaFVars #[a] h₂
        let q₂ ← mkLambdaFVars #[a] b'
        let e' ← mkForallFVarsS #[a] b'
        return .step e' (mkApp6 (mkConst ``forall_prop_domain_congr) p₁ p₂ q₁ q₂ h h₂) (contextDependent := cd)

/--
Simplifies the domain of `∃ a : p₁, q a` when `p₁ : Prop`. If `simp p₁` produces `p₂` with proof
`h : p₁ = p₂`, the result is `∃ a : p₂, q (h.substr a)` (see `exists_prop_congr_dom`). The body
is not simplified here: the result is not marked as done, so the simplifier visits it afterwards
under `a : p₂`. Intended as a pre-method.
-/
public def simpExistsPropDomain : Simproc := fun e => do
  let_expr ex@Exists _ fn := e | return .rfl
  let .lam n p₁ body bi := fn | return .rfl
  unless (← isProp p₁) do return .rfl
  match (← simp p₁) with
  | .rfl _ cd => return mkRflResultCD cd
  | .step p₂ h _ cd =>
    let fn' ← withLocalDeclS n bi p₂ fun a => do
      let h' ← mkPropDomainCastS p₁ p₂ h a
      mkLambdaFVarsS #[a] (← instantiateS body #[h'])
    let e' ← mkAppS₂ ex p₂ fn'
    return .step e' (mkApp4 (mkConst ``exists_prop_congr_dom) p₁ p₂ h fn) (contextDependent := cd)

public def simpForall : Simproc :=
  simpForall' simpArrow simp

end Lean.Meta.Sym.Simp
