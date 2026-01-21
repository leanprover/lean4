/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Simp.SimpM
import Lean.Meta.SynthInstance
import Lean.Meta.Tactic.Simp.Types
import Lean.Meta.Sym.AlphaShareBuilder
import Lean.Meta.Sym.InferType
import Lean.Meta.Sym.Simp.Result
import Lean.Meta.Sym.Simp.CongrInfo
namespace Lean.Meta.Sym.Simp
open Internal

/-!
# Simplifying Application Arguments and Congruence Lemma Application

This module provides functions for building congruence proofs during simplification.
Given a function application `f a₁ ... aₙ` where some arguments are rewritable,
we recursively simplify those arguments (via `simp`) and construct a proof that the
original expression equals the simplified one.

The key challenge is efficiency: we want to avoid repeatedly inferring types, or destroying sharing,
The `CongrInfo` type (see `SymM.lean`) categorizes functions
by their argument structure, allowing us to choose the most efficient proof strategy:

- `fixedPrefix`: Use simple `congrArg`/`congrFun'`/`congr` for trailing arguments. We exploit
  the fact that there are no dependent arguments in the suffix and use the cheaper `congrFun'`
  instead of `congrFun`.
- `interlaced`: Mix rewritable and fixed arguments. It may have to use `congrFun` for fixed
  dependent arguments.
- `congrTheorem`: Apply a pre-generated congruence theorem for dependent arguments

**Design principle**: Never infer the type of proofs. This avoids expensive type
inference on proof terms, which can be arbitrarily complex, and often destroys sharing.
-/

/--
Helper function for constructing a congruence proof using `congrFun'`, `congrArg`, `congr`.
For the dependent case, use `mkCongrFun`
-/
public def mkCongr (e : Expr) (f a : Expr) (fr : Result) (ar : Result) (_ : e = .app f a) : SymM Result := do
  let mkCongrPrefix (declName : Name) : SymM Expr := do
    let α ← inferType a
    let u ← getLevel α
    let β ← inferType e
    let v ← getLevel β
    return mkApp2 (mkConst declName [u, v]) α β
  match fr, ar with
  | .rfl _,  .rfl _ => return .rfl
  | .step f' hf _, .rfl _ =>
    let e' ← mkAppS f' a
    let h := mkApp4 (← mkCongrPrefix ``congrFun') f f' hf a
    return .step e' h
  | .rfl _, .step a' ha _ =>
    let e' ← mkAppS f a'
    let h := mkApp4 (← mkCongrPrefix ``congrArg) a a' f ha
    return .step e' h
  | .step f' hf _, .step a' ha _ =>
    let e' ← mkAppS f' a'
    let h := mkApp6 (← mkCongrPrefix ``congr) f f' a a' hf ha
    return .step e' h

/--
Returns a proof using `congrFun`
```
congrFun.{u, v} {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x} (h : f = g) (a : α) : f a = g a
```
-/
def mkCongrFun (e : Expr) (f a : Expr) (f' : Expr) (hf : Expr) (_ : e = .app f a) (done := false) : SymM Result := do
  let .forallE x _ βx _ ← whnfD (← inferType f)
    | throwError "failed to build congruence proof, function expected{indentExpr f}"
  let α ← inferType a
  let u ← getLevel α
  let v ← getLevel (← inferType e)
  let β := Lean.mkLambda x .default α βx
  let e' ← mkAppS f' a
  let h := mkApp6 (mkConst ``congrFun [u, v]) α β f f' hf a
  return .step e' h done

/--
Handles simplification of over-applied function terms.

When a function has more arguments than expected by its `CongrInfo`, we need to handle
the "extra" arguments separately. This function peels off `numArgs` trailing applications,
simplifies the remaining function using `simpFn`, then rebuilds the term by simplifying
and re-applying the trailing arguments.

**Over-application** occurs when:
- A function with `fixedPrefix prefixSize suffixSize` is applied to more than `prefixSize + suffixSize` arguments
- A function with `interlaced` rewritable mask is applied to more than `mask.size` arguments
- A function with a congruence theorem is applied to more than the theorem expects

**Example**: If `f` has `CongrInfo.fixedPrefix 2 3` (expects 5 arguments) but we see `f a₁ a₂ a₃ a₄ a₅ b₁ b₂`,
then `numArgs = 2` (the extra arguments) and we:
1. Recursively simplify `f a₁ a₂ a₃ a₄ a₅` using the fixed prefix strategy (via `simpFn`)
2. Simplify each extra argument `b₁` and `b₂`
3. Rebuild the term using either `mkCongr` (for non-dependent arrows) or `mkCongrFun` (for dependent functions)

**Parameters**:
- `e`: The over-applied expression to simplify
- `numArgs`: Number of excess arguments to peel off
- `simpFn`: Strategy for simplifying the function after peeling (e.g., `simpFixedPrefix`, `simpInterlaced`, or `simpUsingCongrThm`)

**Note**: This is a fallback path without specialized optimizations. The common case (correct number of arguments)
is handled more efficiently by the specific strategies.
-/
public def simpOverApplied (e : Expr) (numArgs : Nat) (simpFn : Expr → SimpM Result) : SimpM Result := do
  let rec visit (e : Expr) (i : Nat) : SimpM Result := do
    if i == 0 then
      simpFn e
    else
      let i := i - 1
      match h : e with
      | .app f a =>
        let fr ← visit f i
        let .forallE _ α β _ ← whnfD (← inferType f) | unreachable!
        if !β.hasLooseBVars then
          if (← isProp α) then
            mkCongr e f a fr .rfl h
          else
            mkCongr e f a fr (← simp a) h
        else match fr with
          | .rfl _ => return .rfl
          | .step f' hf _ => mkCongrFun e f a f' hf h
      | _ => unreachable!
  visit e numArgs

/--
Handles over-applied function expressions by simplifying only the base function and
propagating changes through extra arguments WITHOUT simplifying them.

Unlike `simpOverApplied`, this function does not simplify the extra arguments themselves.
It only uses congruence (`mkCongrFun`) to propagate changes when the base function is simplified.

**Algorithm**:
1. Peel off `numArgs` extra arguments from `e`
2. Apply `simpFn` to simplify the base function
3. If the base changed, propagate the change through each extra argument using `mkCongrFun`
4. Return `.rfl` if the base function was not simplified

**Parameters**:
- `e`: The over-applied expression
- `numArgs`: Number of excess arguments to peel off
- `simpFn`: Strategy for simplifying the base function after peeling

**Contrast with `simpOverApplied`**:
- `simpOverApplied`: Fully simplifies both base and extra arguments
- `propagateOverApplied`: Only simplifies base, appends extra arguments unchanged
-/
public def propagateOverApplied (e : Expr) (numArgs : Nat) (simpFn : Expr → SimpM Result) : SimpM Result := do
  let rec visit (e : Expr) (i : Nat) : SimpM Result := do
    if i == 0 then
      simpFn e
    else
      let i := i - 1
      match h : e with
      | .app f a =>
        let r ← visit f i
        match r with
        | .rfl _ => return r
        | .step f' hf done => mkCongrFun e f a f' hf h done
      | _ => unreachable!
  visit e numArgs

/--
Reduces `type` to weak head normal form and verifies it is a `forall` expression.
If `type` is already a `forall`, returns it unchanged (avoiding unnecessary work).
The result is shared via `share` to maintain maximal sharing invariants.
-/
def whnfToForall (type : Expr) : SymM Expr := do
  if type.isForall then return type
  let type ← whnfD type
  unless type.isForall do throwError "function type expected{indentD type}"
  share type

/--
Returns the type of an expression `e`. If `n > 0`, then `e` is an application
with at least `n` arguments. This function assumes the `n` trailing arguments are non-dependent.
Given `e` of the form `f a₁ a₂ ... aₙ`, the type of `e` is computed by
inferring the type of `f` and traversing the forall telescope.

We use this function to implement `congrFixedPrefix`. Recall that `inferType` is cached.
This function tries to maximize the likelihood of a cache hit. For example,
suppose `e` is `@HAdd.hAdd Nat Nat Nat instAdd 5` and `n = 1`. It is much more likely that
`@HAdd.hAdd Nat Nat Nat instAdd` is already in the cache than
`@HAdd.hAdd Nat Nat Nat instAdd 5`.
-/
def getFnType (e : Expr) (n : Nat) : SymM Expr := do
  match n with
  | 0 => inferType e
  | n+1 =>
    let type ← getFnType e.appFn! n
    let .forallE _ _ β _ ← whnfToForall type | unreachable!
    return β

/--
Simplifies arguments of a function application with a fixed prefix structure.
Recursively simplifies the trailing `suffixSize` arguments, leaving the first
`prefixSize` arguments unchanged.

For a function with `CongrInfo.fixedPrefix prefixSize suffixSize`, the arguments
are structured as:
```
f a₁ ... aₚ b₁ ... bₛ
  └───────┘ └───────┘
   prefix    suffix (rewritable)
```

The prefix arguments (types, instances) should
not be rewritten directly. Only the suffix arguments are recursively simplified.

**Performance optimization**: We avoid calling `inferType` on applied expressions
like `f a₁ ... aₚ b₁` or `f a₁ ... aₚ b₁ ... bₛ`, which would have poor cache hit rates.
Instead, we infer the type of the function prefix `f a₁ ... aₚ`
(e.g., `@HAdd.hAdd Nat Nat Nat instAdd`) which is probably shared across many applications,
then traverse the forall telescope to extract argument and result types as needed.

The helper `go` returns `Result × Expr` where the `Expr` is the function type at that
position. However, the type is only meaningful (non-`default`) when `Result` is
`.step`, since we only need types for constructing congruence proofs. This avoids
unnecessary type inference when no rewriting occurs.
-/
def simpFixedPrefix (e : Expr) (prefixSize : Nat) (suffixSize : Nat) : SimpM Result := do
  let numArgs := e.getAppNumArgs
  if numArgs ≤ prefixSize then
    -- Nothing to be done
    return .rfl
  else if numArgs > prefixSize + suffixSize then
    simpOverApplied e (numArgs - prefixSize - suffixSize) (main suffixSize)
  else
    main (numArgs - prefixSize) e
where
  main (n : Nat) (e : Expr) : SimpM Result := do
    return (← go n e).1

  go (i : Nat) (e : Expr) : SimpM (Result × Expr) := do
    if i == 0 then
      return (.rfl, default)
    else
      let .app f a := e | unreachable!
      let (hf, fType) ← go (i-1) f
      match hf, (← simp a) with
      | .rfl _,  .rfl _ => return (.rfl, default)
      | .step f' hf _, .rfl _ =>
        let .forallE _ α β _ ← whnfToForall fType | unreachable!
        let e' ← mkAppS f' a
        let u ← getLevel α
        let v ← getLevel β
        let h := mkApp6 (mkConst ``congrFun' [u, v]) α β f f' hf a
        return (.step e' h, β)
      | .rfl _, .step a' ha _ =>
        let fType ← getFnType f (i-1)
        let .forallE _ α β _ ← whnfToForall fType | unreachable!
        let e' ← mkAppS f a'
        let u ← getLevel α
        let v ← getLevel β
        let h := mkApp6 (mkConst ``congrArg [u, v]) α β a a' f ha
        return (.step e' h, β)
      | .step f' hf _, .step a' ha _ =>
        let .forallE _ α β _ ← whnfToForall fType | unreachable!
        let e' ← mkAppS f' a'
        let u ← getLevel α
        let v ← getLevel β
        let h := mkApp8 (mkConst ``congr [u, v]) α β f f' a a' hf ha
        return (.step e' h, β)

/--
Simplifies arguments of a function application with interlaced rewritable/fixed arguments.
Uses `rewritable[i]` to determine whether argument `i` should be simplified.
For rewritable arguments, calls `simp` and uses `congrFun'`, `congrArg`, and `congr`; for fixed arguments,
uses `congrFun` to propagate changes from earlier arguments.
-/
def simpInterlaced (e : Expr) (rewritable : Array Bool) : SimpM Result := do
  let numArgs := e.getAppNumArgs
  if h : numArgs = 0 then
    -- Nothing to be done
    return .rfl
  else if h : numArgs > rewritable.size then
    simpOverApplied e (numArgs - rewritable.size) (go rewritable.size · (Nat.le_refl _))
  else
    go numArgs e (by omega)
where
  go (i : Nat) (e : Expr) (h : i ≤ rewritable.size) : SimpM Result := do
    if h : i = 0 then
      return .rfl
    else
      match h : e with
      | .app f a =>
        let fr ← go (i - 1) f (by omega)
        if rewritable[i - 1] then
          mkCongr e f a fr (← simp a) h
        else match fr with
          | .rfl _ => return .rfl
          | .step f' hf _ => mkCongrFun e f a f' hf h
      | _ => unreachable!

/--
Helper function used at `congrThm`. The idea is to initialize `argResults` lazily
when we get the first non-`.rfl` result.
-/
def pushResult (argResults : Array Result) (numEqs : Nat) (result : Result) : Array Result :=
  match result with
  | .rfl .. => if argResults.size > 0 then argResults.push result else argResults
  | .step .. =>
    if argResults.size < numEqs then
      Array.replicate numEqs .rfl |>.push result
    else
      argResults.push result

/--
Simplifies arguments of a function application using a pre-generated congruence theorem.

This strategy is used for functions that have complex argument dependencies, particularly
those with proof arguments or `Decidable` instances. Unlike `congrFixedPrefix` and
`congrInterlaced`, which construct proofs on-the-fly using basic congruence lemmas
(`congrArg`, `congrFun`, `congrFun'`, `congr`), this function applies a specialized congruence theorem
that was pre-generated for the specific function being simplified.

See type `CongrArgKind`.

**Algorithm**:
1. Recursively simplify all `.eq` arguments (via `simpEqArgs`)
2. If all simplifications return `.rfl`, the overall result is `.rfl`
3. Otherwise, construct the final proof by:
   - Starting with the congruence theorem's proof term
   - Applying original arguments and their simplification results
   - Re-synthesizing subsingleton instances when their dependencies change
   - Removing unnecessary casts from the result

**Key examples**:

1. `ite`: Has type `{α : Sort u} → (c : Prop) → [Decidable c] → α → α → α`
   - Argument kinds: `[.fixed, .eq, .subsingletonInst, .eq, .eq]`
   - When simplifying `ite (x > 0) a b`, if `x > 0` simplifies to `true`, we must
     re-synthesize `[Decidable true]` because the original `[Decidable (x > 0)]`
     instance is no longer type-correct

2. `GetElem.getElem`: Has type
   ```
   {coll : Type u} → {idx : Type v} → {elem : Type w} → {valid : coll → idx → Prop} →
   [GetElem coll idx elem valid] → (xs : coll) → (i : idx) → valid xs i → elem
   ```
   - The proof argument `valid xs i` depends on earlier arguments `xs` and `i`
   - When `xs` or `i` are simplified, the proof is adjusted in the `rhs` of the auto-generated
     theorem.
-/
def simpUsingCongrThm (e : Expr) (thm : CongrTheorem) : SimpM Result := do
  let argKinds := thm.argKinds
  /-
  Constructs the non-`rfl` result. `argResults` contains the result for arguments with kind `.eq`.
  There is at least one non-`rfl` result in `argResults`.
  -/
  let mkNonRflResult (argResults : Array Result) : SimpM Result := do
    let mut proof := thm.proof
    let mut type  := thm.type
    let mut j := 0 -- index at argResults
    let mut subst := #[]
    let args := e.getAppArgs
    for arg in args, kind in argKinds do
      proof := mkApp proof arg
      type := type.bindingBody!
      match kind with
      | .fixed => subst := subst.push arg
      | .cast  => subst := subst.push arg
      | .subsingletonInst =>
        subst := subst.push arg
        let clsNew := type.bindingDomain!.instantiateRev subst
        let instNew ← if (← isDefEqI (← inferType arg) clsNew) then
          pure arg
        else
          let .some val ← trySynthInstance clsNew | return .rfl
          pure val
        proof := mkApp proof instNew
        subst := subst.push instNew
        type := type.bindingBody!
      | .eq =>
        subst := subst.push arg
        match argResults[j]! with
        | .rfl _ =>
          let h ← mkEqRefl arg
          proof := mkApp2 proof arg h
          subst := subst.push arg |>.push h
        | .step arg' h _ =>
          proof := mkApp2 proof arg' h
          subst := subst.push arg' |>.push h
        type := type.bindingBody!.bindingBody!
        j := j + 1
      | _ => unreachable!
    let_expr Eq _ _ rhs := type | unreachable!
    let rhs := rhs.instantiateRev subst
    let hasCast := argKinds.any (· matches .cast)
    let rhs ← if hasCast then Simp.removeUnnecessaryCasts rhs else pure rhs
    let rhs ← share rhs
    return .step rhs proof
  /-
  Recursively simplifies arguments of kind `.eq`. The array `argResults` is initialized lazily
  as soon as the simplifier returns a non-`rfl` result for some arguments.
  `numEqs` is the number of `.eq` arguments found so far.
  -/
  let rec simpEqArgs (e : Expr) (i : Nat) (numEqs : Nat) (argResults : Array Result) : SimpM Result := do
    match e with
    | .app f a =>
      match argKinds[i]! with
      | .subsingletonInst
      | .fixed => simpEqArgs f (i-1) numEqs argResults
      | .cast => simpEqArgs f (i-1) numEqs argResults
      | .eq => simpEqArgs f (i-1) (numEqs+1) (pushResult argResults numEqs (← simp a))
      | _ => unreachable!
    | _ =>
      if argResults.isEmpty then
        return .rfl
      else
        mkNonRflResult argResults.reverse
  let numArgs := e.getAppNumArgs
  if numArgs > argKinds.size then
    simpOverApplied e (numArgs - argKinds.size) (simpEqArgs · (argKinds.size - 1) 0 #[])
  else if numArgs < argKinds.size then
    /-
    **Note**: under-applied case. This can be optimized, but this case is so
    rare that it is not worth doing it. We just reuse `simpOverApplied`
    -/
    simpOverApplied e e.getAppNumArgs (fun _ => return .rfl)
  else
    simpEqArgs e (argKinds.size - 1) 0 #[]

/--
Main entry point for simplifying function application arguments.
Dispatches to the appropriate strategy based on the function's `CongrInfo`.
-/
public def simpAppArgs (e : Expr) : SimpM Result := do
  let f := e.getAppFn
  match (← getCongrInfo f) with
  | .none => return .rfl
  | .fixedPrefix prefixSize suffixSize => simpFixedPrefix e prefixSize suffixSize
  | .interlaced rewritable => simpInterlaced e rewritable
  | .congrTheorem thm => simpUsingCongrThm e thm

/--
Simplifies arguments in a specified range `[start, stop)` of a function application.

Given an expression `f a₀ a₁ ... aₙ`, this function simplifies only the arguments
at positions `start ≤ i < stop`, leaving arguments outside this range unchanged.
Changes are propagated using congruence lemmas.

**Use case**: Useful for control-flow simplification where we want to simplify only
discriminants of a `match` expression without touching the branches.
-/
public def simpAppArgRange (e : Expr) (start stop : Nat) : SimpM Result := do
  let numArgs := e.getAppNumArgs
  assert! start < stop
  if numArgs < start then return .rfl
  let numArgs := numArgs - start
  let stop := stop - start
  let rec visit (e : Expr) (i : Nat) : SimpM Result := do
    if i == 0 then
      return .rfl
    let i := i - 1
    match h : e with
    | .app f a =>
      let fr ← visit f i
      let skip : SimpM Result := do
        match fr with
        | .rfl _ => return .rfl
        | .step f' hf _ => mkCongrFun e f a f' hf h
      if i < stop then
        let .forallE _ α β _ ← whnfD (← inferType f) | unreachable!
        if !β.hasLooseBVars then
          if (← isProp α) then
            mkCongr e f a fr .rfl h
          else
            mkCongr e f a fr (← simp a) h
        else skip
      else skip
    | _ => unreachable!
  visit e numArgs

end Lean.Meta.Sym.Simp
