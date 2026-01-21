/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Simp.SimpM
import Lean.Meta.Sym.AlphaShareBuilder
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
  let w ← getLevel type
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

public def simpForall (e : Expr) : SimpM Result := do
  if e.isArrow then
    simpArrow e
  else if (← isProp e) then
    let n := getForallTelescopeSize e.bindingBody! 1
    forallBoundedTelescope e n fun xs b => withoutModifyingCacheIfNotWellBehaved do
      main xs b
  else
    return .rfl
where
  main (xs : Array Expr) (b : Expr) : SimpM Result := do
    match (← simp b) with
    | .rfl _ => return .rfl
    | .step b' h _ =>
      let h ← mkLambdaFVars xs h
      let e' ← shareCommonInc (← mkForallFVars xs b')
      -- **Note**: consider caching the forall-congr theorems
      let hcongr ← mkForallCongrFor xs
      return .step e' (mkApp3 hcongr (← mkLambdaFVars xs b) (← mkLambdaFVars xs b') h)

  -- **Note**: Optimize if this is quadratic in practice
  getForallTelescopeSize (e : Expr) (n : Nat) : Nat :=
    match e with
    | .forallE _ _ b _ => if b.hasLooseBVar 0 then getForallTelescopeSize b (n+1) else n
    | _ => n

end Lean.Meta.Sym.Simp
