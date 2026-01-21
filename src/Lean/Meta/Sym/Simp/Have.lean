/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Simp.SimpM
import Lean.Meta.Sym.Simp.Lambda
import Lean.Meta.Sym.AlphaShareBuilder
import Lean.Meta.Sym.InstantiateS
import Lean.Meta.Sym.ReplaceS
import Lean.Meta.Sym.AbstractS
import Lean.Meta.Sym.InferType
import Lean.Meta.AppBuilder
import Lean.Meta.HaveTelescope
import Lean.Util.CollectFVars
namespace Lean.Meta.Sym.Simp

/-!
# Have-Telescope Simplification for Sym.simp

This module implements efficient simplification of `have`-telescopes (sequences of
non-dependent `let` bindings) in the symbolic simplifier. The key insight is to
transform telescopes into a "parallel" beta-application form, simplify the arguments
independently, and then convert back to `have` form.

## The Problem

Consider a `have`-telescope:
```
have x₁ := v₁
have x₂ := v₂[x₁]
...
have xₙ := vₙ[x₁, ..., xₙ₋₁]
b[x₁, ..., xₙ]
```

Naively generating proofs using `have_congr` leads to **quadratic kernel type-checking time**.
The issue is that when the kernel type-checks congruence proofs, it creates fresh free
variables for each binder, destroying sharing and generating O(n²) terms.

## The Solution: Virtual Parallelization

We transform the sequential `have` telescope into a parallel beta-application:
```
(fun x₁ x₂' ... xₙ' => b[x₁, x₂' x₁, ..., xₙ' (xₙ₋₁' ...)]) v₁ (fun x₁ => v₂[x₁]) ... (fun ... xₙ₋₁ => vₙ[..., xₙ₋₁])
```

Each `xᵢ'` is now a function that takes its dependencies as arguments. This form:
1. Is definitionally equal to the original (so conversion is free)
2. Enables independent simplification of each argument
3. Produces proofs that type-check in linear time using the existing efficient simplification procedure for lambdas.

## Algorithm Overview

1. **`toBetaApp`**: Transform `have`-telescope → parallel beta-application
   - Track dependency graph: which `have` depends on which previous `have`s
   - Convert each value `vᵢ[x₁, ..., xₖ]` to `(fun y₁ ... yₖ => vᵢ[y₁, ..., yₖ])`
   - Build the body with appropriate applications

2. **`simpBetaApp`**: Simplify the beta-application using congruence lemmas
   - Simplify function and each argument independently
   - Generate proof using `congr`, `congrArg`, `congrFun'`
   - This procedure is optimized for functions taking **many** arguments.

3. **`toHave`**: Convert simplified beta-application → `have`-telescope
   - Reconstruct the `have` bindings from the lambda structure
   - Apply each argument to recover original variable references
-/

/--
Result of converting a `have`-telescope to a parallel beta-application.

Given:
```
have x₁ := v₁; have x₂ := v₂[x₁]; ...; have xₙ := vₙ[...]; b[x₁, ..., xₙ]
```

We produce:
```
(fun x₁ x₂' ... xₙ' => b'[...]) v₁ (fun deps => v₂[deps]) ... (fun deps => vₙ[deps])
```

where each `xᵢ'` has type `deps_type → Tᵢ` and `b'` contains applications `xᵢ' (deps)`.
-/
structure ToBetaAppResult where
  /-- Type of the input `have`-expression. -/
  α : Expr
  /-- The universe level of `α`. -/
  u : Level
  /-- The beta-application form: `(fun x₁ ... xₙ' => b') v₁ ... (fun deps => vₙ)`. -/
  e : Expr
  /-- Proof that the original expression equals `e` (by reflexivity + hints, since definitionally equal). -/
  h : Expr
  /--
  Dependency information for each `have`.
  `varDeps[i]` contains the indices of previous `have`s that `vᵢ` depends on.
  Used by `toHave` to reconstruct the telescope.
  -/
  varDeps : Array (Array Nat)
  /--
  The function type: `T₁ → (deps₁ → T₂) → ... → (depsₙ₋₁ → Tₙ) → β`.
  Used to compute universe levels for congruence lemmas.
  -/
  fType : Expr
  deriving Inhabited

/--
Collect free variable Ids that appear in `e` and are tracked in `fvarIdToPos`,
sorted by their position in the telescope.
-/
def collectFVarIdsAt (e : Expr) (fvarIdToPos : FVarIdMap Nat) : Array FVarId :=
  let s := collectFVars {} e
  let fvarIds := s.fvarIds.filter (fvarIdToPos.contains ·)
  fvarIds.qsort fun fvarId₁ fvarId₂ =>
    let pos₁ := fvarIdToPos.get! fvarId₁
    let pos₂ := fvarIdToPos.get! fvarId₂
    pos₁ < pos₂

open Internal in
/--
Build a chain of arrows `α₁ → α₂ → ... → αₙ → β` using the `mkForallS` wrapper
(not `.forallE`) to preserve sharing.
-/
def mkArrows (αs : Array Expr) (β : Expr) : SymM Expr := do
  go αs.size β (Nat.le_refl _)
where
  go (i : Nat) (β : Expr) (h : i ≤ αs.size) : SymM Expr := do
    match i with
    | 0 => return β
    | i+1 => go i (← mkForallS `a .default αs[i] β) (by omega)

/--
Transform a `have`-telescope into a parallel beta-application.

**Input**: `have x₁ := v₁; ...; have xₙ := vₙ; b`

**Output**: A `ToBetaAppResult` containing the equivalent beta-application.

## Transformation Details

For each `have xᵢ := vᵢ` where `vᵢ` depends on `xᵢ₁, ..., xᵢₖ` (aka `depsₖ`)
- The argument becomes `fun depsₖ => vᵢ[depsₖ]`
- The type becomes `Dᵢ₁ → ... → Dᵢₖ → Tᵢ` where `Dᵢⱼ` is the type of `xᵢⱼ`
- In the body, `xᵢ` is replaced by `xᵢ' sᵢ₁ ... sᵢₖ` where `sᵢⱼ` is the replacement for `xᵢⱼ`

The proof is `rfl` since the transformation is definitionally equal.
-/
def toBetaApp (haveExpr : Expr) : SymM ToBetaAppResult := do
  go haveExpr #[] #[] #[] #[] #[] #[] {}
where
  /--
  Process the telescope recursively.

  - `e`: Current expression (remaining telescope)
  - `xs`: Original `have` binders (as fvars)
  - `xs'`: New binders with function types (as fvars)
  - `args`: Lambda-wrapped values `(fun deps => vᵢ)`
  - `subst`: Substitution mapping old vars to applications `xᵢ' sᵢ₁ ... sᵢₖ`
  - `types`: Types of the new binders
  - `varDeps`: Dependency positions for each `have`
  - `fvarIdToPos`: Map from fvar ID to telescope position
  -/
  go (e : Expr) (xs xs' args subst types : Array Expr) (varDeps : Array (Array Nat)) (fvarIdToPos : FVarIdMap Nat)
      : SymM ToBetaAppResult := do
    if let .letE n t v b (nondep := true) := e then
      assert! !t.hasLooseBVars
      withLocalDeclD n t fun x => do
      let v := v.instantiateRev xs
      let fvarIds := collectFVarIdsAt v fvarIdToPos
      let varPos := fvarIds.map (fvarIdToPos.getD · 0)
      let ys := fvarIds.map mkFVar
      let arg ← mkLambdaFVars ys v
      let t' ← share (← mkForallFVars ys t)
      withLocalDeclD n t' fun x' => do
      let args' := fvarIds.map fun fvarId =>
        let pos := fvarIdToPos.get! fvarId
        subst[pos]!
      let v' ← share <| mkAppN x' args'
      let fvarIdToPos := fvarIdToPos.insert x.fvarId! xs.size
      go b (xs.push x) (xs'.push x') (args.push arg) (subst.push v') (types.push t') (varDeps.push varPos) fvarIdToPos
    else
      let e ← instantiateRevS e subst
      let α ← inferType e
      let u ← getLevel α
      let fType ← mkArrows types α
      let e ← mkLambdaFVarsS xs' e
      let e ← share <| mkAppN e args
      let eq := mkApp3 (mkConst ``Eq [u]) α haveExpr e
      let h := mkApp2 (mkConst ``Eq.refl [u]) α haveExpr
      let h := mkExpectedPropHint h eq
      return { α, u, e, h, varDeps, fType }

/--
Strip `n` leading forall binders from a type.
Used to extract the actual type from a function type when we know the number of arguments.
-/
def consumeForallN (type : Expr) (n : Nat) : Expr :=
  match n with
  | 0 => type
  | n+1 => consumeForallN type.bindingBody! n

open Internal in
/--
Eliminate auxiliary applications `xᵢ' sᵢ₁ ... sᵢₖ` in the body when converting back to `have` form.

After simplification, the body contains applications like `xᵢ' deps`. This function
replaces them with the actual `have` variables `xᵢ`.

**Parameters**:
- `e`: Expression containing `xᵢ' deps` applications (with loose bvars)
- `xs`: The actual `have` binders to substitute in
- `varDeps`: Dependency information for each variable

The function uses `replaceS` to traverse `e`, looking for applications of
bound variables at the expected positions.
-/
def elimAuxApps (e : Expr) (xs : Array Expr) (varDeps : Array (Array Nat)) : SymM Expr := do
  let n := xs.size
  replaceS e fun e offset => do
    if offset >= e.looseBVarRange then
      return some e
    match e.getAppFn with
    | .bvar idx =>
      if _h : idx >= offset then
        if _h : idx < offset + n then
          let i := n - (idx - offset) - 1
          let expectedNumArgs := varDeps[i]!.size
          let numArgs := e.getAppNumArgs
          if numArgs > expectedNumArgs then
            return none -- Over-applied
          else
            assert! numArgs == expectedNumArgs
            return xs[i]
        else
          mkBVarS (idx - n)
      else
        return some e
    | _ => return none

/--
Convert a simplified beta-application back to `have` form.

**Input**: `(fun x₁ ... xₙ' => b') v₁ ... vₙ` with dependency info

**Output**: `have x₁ := w₁; ...; have xₙ := wₙ; b`
-/
def toHave (e : Expr) (varDeps : Array (Array Nat)) : SymM Expr :=
  e.withApp fun f args => do
  if _h : args.size ≠ varDeps.size then unreachable! else
  let rec go (f : Expr) (xs : Array Expr) (i : Nat) : SymM Expr := do
    if _h : i < args.size then
      let .lam n t b _ := f | unreachable!
      let varPos := varDeps[i]
      let ys := varPos.map fun i => xs[i]!
      let type := consumeForallN t varPos.size
      let val ← share <| args[i].betaRev ys
      withLetDecl (nondep := true) n type val fun x => do
      go b (xs.push (← share x)) (i+1)
    else
      let f ← elimAuxApps f xs varDeps
      let result ← mkLetFVars (generalizeNondepLet := false) (usedLetOnly := false) xs f
      share result
  go f #[] 0

/-- Result of extracting universe levels from a non-dependent function type. -/
structure GetUnivsResult where
  /-- Universe level of each argument type. -/
  argUnivs : Array Level
  /-- Universe level of each partial application's result type. -/
  fnUnivs : Array Level

/--
Extract universe levels from a function type for use in congruence lemmas.

For `α₁ → α₂ → ... → αₙ → β`:
- `argUnivs[i]` = universe of `αᵢ₊₁`
- `fnUnivs[i]` = universe of `αᵢ₊₁ → ... → β`

These are needed because `congr`, `congrArg`, and `congrFun'` are universe-polymorphic,
and we want to avoid a quadratic overhead.
-/
def getUnivs (fType : Expr) : SymM GetUnivsResult := do
  go fType #[]
where
  go (type : Expr) (argUnivs : Array Level) : SymM GetUnivsResult := do
    match type with
    | .forallE _ d b _ =>
      go b (argUnivs.push (← getLevel d))
    | _ =>
      let mut v ← getLevel type
      let mut i := argUnivs.size
      let mut fnUnivs := #[]
      while i > 0 do
        i := i - 1
        let u := argUnivs[i]!
        v := mkLevelIMax' u v |>.normalize
        fnUnivs := fnUnivs.push v
      fnUnivs := fnUnivs.reverse
      return { argUnivs, fnUnivs }

open Internal in
/--
Simplify a beta-application and generate a proof.

This is the core simplification routine. Given `f a₁ ... aₙ`, it:
1. Simplifies `f` and each `aᵢ` independently
2. Combines the results using appropriate congruence lemmas

## Congruence Lemma Selection

For each application `f a`:
- If both changed: use `congr : f = f' → a = a' → f a = f' a'`
- If only `f` changed: use `congrFun' : f = f' → f a = f' a`
- If only `a` changed: use `congrArg : a = a' → f a = f a'`
- If neither changed: return `.rfl`
-/
def simpBetaApp (e : Expr) (fType : Expr) (fnUnivs argUnivs : Array Level) : SimpM Result := do
  return (← go e 0).1
where
  go (e : Expr) (i : Nat) : SimpM (Result × Expr) := do
    match e with
    | .app f a =>
      let (rf, fType) ← go f (i+1)
      let r ← match rf, (← simp a) with
        | .rfl _, .rfl _ =>
          pure .rfl
        | .step f' hf _, .rfl _ =>
          let e' ← mkAppS f' a
          let h := mkApp4 (← mkCongrPrefix ``congrFun' fType i) f f' hf a
          pure <| .step e' h
        | .rfl _, .step a' ha _ =>
          let e' ← mkAppS f a'
          let h := mkApp4 (← mkCongrPrefix ``congrArg fType i) a a' f ha
          pure <| .step e' h
        | .step f' hf _, .step a' ha _ =>
          let e' ← mkAppS f' a'
          let h := mkApp6 (← mkCongrPrefix ``congr fType i) f f' a a' hf ha
          pure <| .step e' h
      return (r, fType.bindingBody!)
    | .lam .. => return (← simpLambda e, fType)
    | _ => unreachable!

  mkCongrPrefix (declName : Name) (fType : Expr) (i : Nat) : SymM Expr := do
    let α := fType.bindingDomain!
    let β := fType.bindingBody!
    let u := argUnivs[i]!
    let v := fnUnivs[i]!
    return mkApp2 (mkConst declName [u, v]) α β

/-- Intermediate result for `have`-telescope simplification. -/
structure SimpHaveResult where
  result : Result
  α : Expr
  u : Level

/--
Core implementation of `have`-telescope simplification.

## Algorithm

1. Convert the `have`-telescope to beta-application form (`toBetaApp`)
2. Simplify the beta-application (`simpBetaApp`)
3. If changed, convert back to `have` form (`toHave`)
4. Chain the proofs using transitivity

## Proof Structure

```
e₁ = e₂    (by rfl, definitional equality from toBetaApp)
e₂ = e₃    (from simpBetaApp)
e₃ = e₄    (by rfl, definitional equality from toHave)
─────────────────────────────────────────────────────────
e₁ = e₄    (by transitivity)
```
-/
def simpHaveCore (e : Expr) : SimpM SimpHaveResult := do
  let e₁ := e
  let r ← toBetaApp e₁
  let e₂ := r.e
  let { fnUnivs, argUnivs } ← getUnivs r.fType
  match (← simpBetaApp e₂ r.fType fnUnivs argUnivs) with
  | .rfl _ => return { result := .rfl, α := r.α, u := r.u }
  | .step e₃ h _ =>
    let h₁ := mkApp6 (mkConst ``Eq.trans [r.u]) r.α e₁ e₂ e₃ r.h h
    let e₄ ← toHave e₃ r.varDeps
    let eq := mkApp3 (mkConst ``Eq [r.u]) r.α e₃ e₄
    let h₂ := mkApp2 (mkConst ``Eq.refl [r.u]) r.α e₃
    let h₂ := mkExpectedPropHint h₂ eq
    let h  := mkApp6 (mkConst ``Eq.trans [r.u]) r.α e₁ e₃ e₄ h₁ h₂
    return { result := .step e₄ h, α := r.α, u := r.u }

/--
Simplify a `have`-telescope.

This is the main entry point for `have`-telescope simplification in `Sym.simp`.
See module documentation for the algorithm overview.
-/
public def simpHave (e : Expr) : SimpM Result := do
  return (← simpHaveCore e).result

/--
Simplify a `have`-telescope and eliminate unused bindings.

This combines simplification with dead variable elimination in a single pass,
avoiding quadratic behavior from multiple passes.
-/
public def simpHaveAndZetaUnused (e₁ : Expr) : SimpM Result := do
  let r ← simpHaveCore e₁
  match r.result with
  | .rfl _ =>
    let e₂ ← zetaUnused e₁
    if isSameExpr e₁ e₂ then
      return .rfl
    else
      let h := mkApp2 (mkConst ``Eq.refl [r.u]) r.α e₂
      return .step e₂ h
  | .step e₂ h _ =>
    let e₃ ← zetaUnused e₂
    if isSameExpr e₂ e₃ then
      return r.result
    else
      let h := mkApp6 (mkConst ``Eq.trans [r.u]) r.α e₁ e₂ e₃ h
        (mkApp2 (mkConst ``Eq.refl [r.u]) r.α e₃)
      return .step e₃ h

public def simpLet (e : Expr) : SimpM Result := do
  if !e.letNondep! then
    /-
    **Note**: We don't do anything if it is a dependent `let`.
    Users may decide to `zeta`-expand them or apply `letToHave` at `pre`/`post`.
    -/
    return .rfl
  else
    simpHaveAndZetaUnused e

end Lean.Meta.Sym.Simp
