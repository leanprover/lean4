/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

prelude
import Lean.Meta.Basic
import Lean.Meta.Match.MatcherApp.Transform
import Lean.Meta.Check
import Lean.Meta.Tactic.Cleanup
import Lean.Meta.Tactic.Subst
import Lean.Meta.Injective -- for elimOptParam
import Lean.Meta.ArgsPacker
import Lean.Elab.PreDefinition.WF.Eqns
import Lean.Elab.PreDefinition.Structural.Eqns
import Lean.Elab.Command
import Lean.Meta.Tactic.ElimInfo

/-!
This module contains code to derive, from the definition of a recursive function (structural or
well-founded, possibly mutual), a **functional induction principle** tailored to proofs about that
function(s).

For example from:
```
def ackermann : Nat → Nat → Nat
  | 0, m => m + 1
  | n+1, 0 => ackermann n 1
  | n+1, m+1 => ackermann n (ackermann (n + 1) m)
```
we get
```
ackermann.induct (motive : Nat → Nat → Prop) (case1 : ∀ (m : Nat), motive 0 m)
  (case2 : ∀ (n : Nat), motive n 1 → motive (Nat.succ n) 0)
  (case3 : ∀ (n m : Nat), motive (n + 1) m → motive n (ackermann (n + 1) m) → motive (Nat.succ n) (Nat.succ m))
  (x x : Nat) : motive x x
```

## Specification

The functional induction principle takes the same fixed parameters as the function, and
the motive takes the same non-fixed parameters as the original function.

For each branch of the original function, there is a case in the induction principle.
Here "branch" roughly corresponds to tail-call positions: branches of top-level
`if`-`then`-`else` and of `match` expressions.

For every recursive call in that branch, an induction hypothesis asserting the
motive for the arguments of the recursive call is provided.
If the recursive call is under binders and it, or its proof of termination,
depend on the the bound values, then these become assumptions of the inductive
hypothesis.

Additionally, the local context of the branch (e.g. the condition of an
if-then-else; a let-binding, a have-binding) is provided as assumptions in the
corresponding induction case, if they are likely to be useful (as determined
by `MVarId.cleanup`).

Mutual recursion is supported and results in multiple motives.


## Implementation overview (well-founded recursion)

For a non-mutual, unary function `foo` (or else for the `_unary` function), we

1. expect its definition, possibly after some `whnf`’ing, to be of the form
   ```
   def foo := fun x₁ … xₙ (y : a) => WellFounded.fix (fun y' oldIH => body) y
   ```
   where `xᵢ…` are the fixed parameter prefix and `y` is the varying parameter of
   the function.

2. From this structure we derive the type of the motive, and start assembling the induction
   principle:
   ```
   def foo.induct := fun x₁ … xₙ (motive : (y : a) → Prop) =>
    fix (fun y' newIH => T[body])
   ```

3. The first phase, transformation `T1[body]` (implemented in) `buildInductionBody`,
   mirrors the branching structure of `foo`, i.e. replicates `dite` and some matcher applications,
   while adjusting their motive. It also unfolds calls to `oldIH` and collects induction hypotheses
   in conditions (see below).

   In particular, when translating a `match` it is prepared to recognize the idiom
   as introduced by `mkFix` via `Lean.Meta.MatcherApp.addArg?`, which refines the type of `oldIH`
   throughout the match. The transformation will replace `oldIH` with `newIH` here.
   ```
        T[(match (motive := fun oldIH => …) y with | … => fun oldIH' => body) oldIH]
    ==> (match (motive := fun newIH => …) y with | … => fun newIH' => T[body]) newIH
   ```

   In addition, the information gathered from the match is preserved, so that when performing the
   proof by induction, the user can reliably enter the right case. To achieve this

   * the matcher is replaced by its splitter, which brings extra assumptions into scope when
     patterns are overlapping
   * simple discriminants that are mentioned in the goal (i.e plain parameters) are instantiated
     in the code.
   * for discriminants that are not instantiated that way, equalities connecting the discriminant
     to the instantiation are added (just as if the user wrote `match h : x with …`)

4. When a tail position (no more branching) is found, function `buildInductionCase` assembles the
   type of the case: a fresh `MVar` asserts the current goal, unwanted values from the local context
   are cleared, and the current `body` is searched for recursive calls using `collectIHs`,
   which are then asserted as inductive hyptheses in the `MVar`.

5. The function `collectIHs` walks the term and collects the induction hypotheses for the current case
   (with proofs). When it encounters a saturated application of `oldIH x proof`, it returns
   `newIH x proof : motive x`.

   Since `x` and `proof` can contain further recursive calls, it uses
   `foldCalls` to replace these with calls to `foo`. This assumes that the
   termination proof `proof` works nevertheless.

   Again, `collectIHs` may encounter the `Lean.Meta.Matcherapp.addArg?` idiom, and again it threads `newIH`
   through, replacing the extra argument. The resulting type of this induction hypothesis is now
   itself a `match` statement (cf. `Lean.Meta.MatcherApp.inferMatchType`)

   The termination proof of `foo` may have abstracted over some proofs; these proofs must be transferred, so
   auxillary lemmas are unfolded if needed.

6. The function `foldCalls` replaces calls to `oldIH` with calls to `foo` that
   make sense to the user.

   At the end of this transformation, no mention of `oldIH` must remain.

7. After this construction, the MVars introduced by `buildInductionCase` are turned into parameters.

The resulting term then becomes `foo.induct` at its inferred type.

## Implementation overview (mutual/non-unary well-founded recursion)

If `foo` is not unary and/or part of a mutual reduction, then the induction theorem for `foo._unary`
(i.e. the unary non-mutual recursion function produced by the equation compiler)
of the form
```
foo._unary.induct : {motive : (a ⊗' b) ⊕' c → Prop} →
  (case1 : ∀ …, motive (PSum.inl (x,y)) →  …) → … →
  (x : (a ⊗' b) ⊕' c) → motive x
```
will first in `unpackMutualInduction` be turned into a joint induction theorem of the form
```
foo.mutual_induct : {motive1 : a → b → Prop} {motive2 : c → Prop} →
  (case1 : ∀ …, motive1 x y  →  …) → … →
  ((x : a) → (y : b) → motive1 x y) ∧ ((z : c) → motive2 z)
```
where all the `PSum`/`PSigma` encoding has been resolved. This theorem is attached to the
name of the first function in the mutual group, like the `._unary` definition.

Finally, in `deriveUnpackedInduction`, for each of the funtions in the mutual group, a simple
projection yields the final `foo.induct` theorem:
```
foo.induct : {motive1 : a → b → Prop} {motive2 : c → Prop} →
  (case1 : ∀ …, motive1 x y  →  …) → … →
  (x : a) → (y : b) → motive1 x y
```

## Implementation overview (structural recursion)

When handling structural recursion, the overall approach is the same, with the following
differences:

* Instead of `WellFounded.fix` we look for a `.brecOn` application, using `isBRecOnRecursor`

  Despite its name, this function does *not* recognize the `.brecOn` of inductive *predicates*,
  which we also do not support at this point.

* The elaboration of structurally recursive function can handle extra arguments. We keep the
  `motive` parameters in the original order.

* The “induction hyothesis” in a `.brecOn` call is a `below x` term that contains all the possible
  recursive calls, whic are projected out using `.fst.snd.…`. The `is_wf` flag that we pass down
  tells us which form of induction hypothesis we are looking for.

* If we have nested recursion (`foo n (foo m acc))`), then we need to infer the argument `m` of the
  nested call `ih.fst.snd acc`. To do so reliably, we replace the `ih` with the “new `ih`”, which
  will have type `motive m acc`, and since `motive` is a FVar we can then read off the arguments
  off this nicely.

* There exist inductive types where the `.brecOn` only supports motives producing `Type u`, but
  not `Sort u`, but our induction principles produce `Prop`. We recognize this case and, rather
  hazardously, replace `.brecOn` with `.binductionOn` (and thus `.below ` with `.ibelow` and
  `PProd` with `And`). This assumes that these definitions are highly analogous.

-/


set_option autoImplicit false

namespace Lean.Tactic.FunInd

open Lean Elab Meta

/-- Opens the body of a lambda, _without_ putting the free variable into the local context.
This is used when replacing parameters with different expressions.
This way it will not be picked up by metavariables.
-/
def removeLamda {n} [MonadLiftT MetaM n] [MonadError n] [MonadNameGenerator n] [Monad n] {α} (e : Expr) (k : FVarId → Expr → n α) : n α := do
  let .lam _n _d b _bi := ← whnfD e | throwError "removeLamda: expected lambda, got {e}"
  let x ← mkFreshFVarId
  let b := b.instantiate1 (.fvar x)
  k x b

/-- `PProd.fst` or `And.left` -/
def mkFst (e : Expr) : MetaM Expr := do
  let t ← whnf (← inferType e)
  match_expr t with
  | PProd _ _ => mkAppM ``PProd.fst #[e]
  | And _ _ => mkAppM ``And.left #[e]
  | _ => throwError "Cannot project out of{indentExpr e}\nof Type{indentExpr t}"

/-- `PProd.snd` or `And.right` -/
def mkSnd (e : Expr) : MetaM Expr := do
  let t ← whnf (← inferType e)
  match_expr t with
  | PProd _ _ => mkAppM ``PProd.snd #[e]
  | And _ _ => mkAppM ``And.right #[e]
  | _ => throwError "Cannot project out of{indentExpr e}\nof Type{indentExpr t}"

/--
Structural recursion only:
Recognizes `oldIH.fst.snd a₁ a₂` and returns `newIH.fst.snd`.
Possibly switching from `PProd.fst` to `And.left` if needed
 -/
partial def isPProdProj (oldIH newIH : FVarId) (e : Expr) : MetaM (Option Expr) := do
  if e.isAppOfArity ``PProd.fst 3 then
    if let some e' ← isPProdProj oldIH newIH e.appArg! then
      return some (← mkFst e')
    else
      return none
  else if e.isAppOfArity ``PProd.snd 3 then
    if let some e' ← isPProdProj oldIH newIH e.appArg! then
      return some (← mkSnd e')
    else
      return none
  else if e.isFVarOf oldIH then
    return some (mkFVar newIH)
  else
    return none

/--
Structural recursion only:
Recognizes `oldIH.fst.snd a₁ a₂` and returns `newIH.fst.snd` and `#[a₁, a₂]`.
-/
def isPProdProjWithArgs (oldIH newIH : FVarId) (e : Expr) : MetaM (Option (Expr × Array Expr)) := do
  if e.isAppOf ``PProd.fst || e.isAppOf ``PProd.snd then
    let arity := e.getAppNumArgs
    unless 3 ≤ arity do return none
    let args := e.getAppArgsN (arity - 3)
    if let some e' ← isPProdProj oldIH newIH (e.stripArgsN (arity - 3)) then
      return some (e', args)
  return none

/--
Replace calls to oldIH back to calls to the original function. At the end, if `oldIH` occurs, an
error is thrown.

The `newIH` will not show up in the output of `foldCalls`, we use it as a helper to infer the
argument of nested recursive calls when we have structural recursion.
-/
partial def foldCalls (is_wf : Bool) (fn : Expr) (oldIH newIH : FVarId) (e : Expr) : MetaM Expr := do
  unless e.containsFVar oldIH do
    return e

  if is_wf then
    if e.getAppNumArgs = 2 && e.getAppFn.isFVarOf oldIH then
      let #[arg, _proof] := e.getAppArgs | unreachable!
      let arg' ← foldCalls is_wf fn oldIH newIH arg
      return .app fn arg'
  else
    if let some (e', args) ← isPProdProjWithArgs oldIH newIH e then
      let t ← whnf (← inferType e')
      let e' ← forallTelescopeReducing t fun xs t' => do
        unless t'.getAppFn.eta.isFVar do -- we expect an application of the `motive` FVar here
          throwError m!"Unexpected type {t} of {e'}: Reduced to application of {t'.getAppFn}"
        mkLambdaFVars xs (fn.beta t'.getAppArgs)
      let args' ← args.mapM (foldCalls is_wf fn oldIH newIH)
      let e' := e'.beta args'
      unless ← isTypeCorrect e' do
        throwError m!"foldCalls: type incorrect after replacing recursive call:{indentExpr e'}"
      return e'

  if let some matcherApp ← matchMatcherApp? e (alsoCasesOn := true) then
    if matcherApp.remaining.size == 1 && matcherApp.remaining[0]!.isFVarOf oldIH then
      let matcherApp' ← matcherApp.transform
        (onParams := foldCalls is_wf fn oldIH newIH)
        (onMotive := fun _motiveArgs motiveBody => do
          let some (_extra, body) := motiveBody.arrow? | throwError "motive not an arrow"
          foldCalls is_wf fn oldIH newIH body)
        (onAlt := fun _altType alt => do
          removeLamda alt fun oldIH alt => do
            foldCalls is_wf fn oldIH newIH alt)
        (onRemaining := fun _ => pure #[])
      return matcherApp'.toExpr

  if e.getAppArgs.any (·.isFVarOf oldIH) then
    -- Sometimes Fix.lean abstracts over oldIH in a proof definition.
    -- So beta-reduce that definition.

    -- Need to look through theorems here!
    let e' ← withTransparency .all do whnf e
    if e == e' then
      throwError "foldCalls: cannot reduce application of {e.getAppFn} in {indentExpr e} "
    return ← foldCalls is_wf fn oldIH newIH e'

  if let some (n, t, v, b) := e.letFun? then
    let t' ← foldCalls is_wf fn oldIH newIH t
    let v' ← foldCalls is_wf fn oldIH newIH v
    return ← withLocalDecl n .default t' fun x => do
      let b' ← foldCalls is_wf fn oldIH newIH (b.instantiate1 x)
      mkLetFun x v' b'

  match e with
  | .app e1 e2 =>
    return .app (← foldCalls is_wf fn oldIH newIH e1) (← foldCalls is_wf fn oldIH newIH e2)

  | .lam n t body bi =>
    let t' ← foldCalls is_wf fn oldIH newIH t
    return ← withLocalDecl n bi t' fun x => do
      let body' ← foldCalls is_wf fn oldIH newIH (body.instantiate1 x)
      mkLambdaFVars #[x] body'

  | .forallE n t body bi =>
    let t' ← foldCalls is_wf fn oldIH newIH t
    return ← withLocalDecl n bi t' fun x => do
      let body' ← foldCalls is_wf fn oldIH newIH (body.instantiate1 x)
      mkForallFVars #[x] body'

  | .letE n t v b _ =>
    let t' ← foldCalls is_wf fn oldIH newIH t
    let v' ← foldCalls is_wf fn oldIH newIH v
    return ← withLetDecl n t' v' fun x => do
      let b' ← foldCalls is_wf fn oldIH newIH (b.instantiate1 x)
      mkLetFVars  #[x] b'

  | .mdata m b =>
    return .mdata m (← foldCalls is_wf fn oldIH newIH b)

  | .proj t i e =>
    return .proj t i (← foldCalls is_wf fn oldIH newIH e)

  | .sort .. | .lit .. | .const .. | .mvar .. | .bvar .. =>
    unreachable! -- cannot contain free variables, so early exit above kicks in

  | .fvar .. =>
    throwError m!"collectIHs: cannot eliminate unsaturated call to induction hypothesis"


/-
In non-tail-positions, we collect the induction hypotheses from all the recursive calls.
-/
-- We could run `collectIHs` and `foldCalls` together, and save a few traversals. Not sure if it
-- worth the extra code complexity.
-- Also, this way of collecting arrays is not as efficient as a left-fold, but we do not expect
-- large arrays here.
partial def collectIHs (is_wf : Bool) (fn : Expr) (oldIH newIH : FVarId) (e : Expr) : MetaM (Array Expr) := do
  unless e.containsFVar oldIH do
    return #[]

  if is_wf then
    if e.getAppNumArgs = 2 && e.getAppFn.isFVarOf oldIH then
      let #[arg, proof] := e.getAppArgs  | unreachable!

      let arg' ← foldCalls is_wf fn oldIH newIH arg
      let proof' ← foldCalls is_wf fn oldIH newIH proof
      let ihs ← collectIHs is_wf fn oldIH newIH arg

      return ihs.push (mkApp2 (.fvar newIH) arg' proof')
  else
    if let some (e', args) ← isPProdProjWithArgs oldIH newIH e then
      let args' ← args.mapM (foldCalls is_wf fn oldIH newIH)
      let ihs ← args.concatMapM (collectIHs is_wf fn oldIH newIH)
      let t ← whnf (← inferType e')
      let arity ← forallTelescopeReducing t fun xs t' => do
        unless t'.getAppFn.eta.isFVar do -- we expect an application of the `motive` FVar here
          throwError m!"Unexpected type {t} of {e'}: Reduced to application of {t'.getAppFn}"
        pure xs.size
      let e' := mkAppN e' args'[:arity]
      let eTyp ← inferType e'
      -- The inferred type that comes out of motive projections has beta redexes
      let eType' := eTyp.headBeta
      return ihs.push (← mkExpectedTypeHint e' eType')


  if let some (n, t, v, b) := e.letFun? then
    let ihs1 ← collectIHs is_wf fn oldIH newIH v
    let v' ← foldCalls is_wf fn oldIH newIH v
    return ← withLetDecl n t v' fun x => do
      let ihs2 ← collectIHs is_wf fn oldIH newIH (b.instantiate1 x)
      let ihs2 ← ihs2.mapM (mkLetFVars (usedLetOnly := true) #[x] ·)
      return ihs1 ++ ihs2


  if let some matcherApp ← matchMatcherApp? e (alsoCasesOn := true) then
    if matcherApp.remaining.size == 1 && matcherApp.remaining[0]!.isFVarOf oldIH then

      let matcherApp' ← matcherApp.transform
        (onParams := foldCalls is_wf fn oldIH newIH)
        (onMotive := fun xs _body => do
          -- Remove the old IH that was added in mkFix
          let eType ← newIH.getType
          let eTypeAbst ← matcherApp.discrs.size.foldRevM (init := eType) fun i eTypeAbst => do
            let motiveArg := xs[i]!
            let discr     := matcherApp.discrs[i]!
            let eTypeAbst ← kabstract eTypeAbst discr
            return eTypeAbst.instantiate1 motiveArg

          -- Will later be overriden with a type that’s itself a match
          -- statement and the infered alt types
          let dummyGoal := mkConst ``True []
          mkArrow eTypeAbst dummyGoal)
        (onAlt := fun altType alt => do
          removeLamda alt fun oldIH' alt => do
            forallBoundedTelescope altType (some 1) fun newIH' _goal' => do
              let #[newIH'] := newIH' | unreachable!
              let altIHs ← collectIHs is_wf fn oldIH' newIH'.fvarId! alt
              let altIH ← mkAndIntroN altIHs
              mkLambdaFVars #[newIH'] altIH)
        (onRemaining := fun _ => pure #[mkFVar newIH])
      let matcherApp'' ← matcherApp'.inferMatchType

      return #[ matcherApp''.toExpr ]

  if e.getAppArgs.any (·.isFVarOf oldIH) then
    -- Sometimes Fix.lean abstracts over oldIH in a proof definition.
    -- So beta-reduce that definition.

    -- Need to look through theorems here!
    let e' ← withTransparency .all do whnf e
    if e == e' then
      throwError "collectIHs: cannot reduce application of {e.getAppFn} in {indentExpr e} "
    return ← collectIHs is_wf fn oldIH newIH e'

  if e.getAppArgs.any (·.isFVarOf oldIH) then
    throwError "collectIHs: could not collect recursive calls from call {indentExpr e}"

  match e with
  | .letE n t v b _ =>
    let ihs1 ← collectIHs is_wf fn oldIH newIH v
    let v' ← foldCalls is_wf fn oldIH newIH v
    return ← withLetDecl n t v' fun x => do
      let ihs2 ← collectIHs is_wf fn oldIH newIH (b.instantiate1 x)
      let ihs2 ← ihs2.mapM (mkLetFVars (usedLetOnly := true) #[x] ·)
      return ihs1 ++ ihs2

  | .app e1 e2 =>
    return (← collectIHs is_wf fn oldIH newIH e1) ++ (← collectIHs is_wf fn oldIH newIH e2)

  | .proj _ _ e =>
    return ← collectIHs is_wf fn oldIH newIH e

  | .forallE n t body bi =>
    let t' ← foldCalls is_wf fn oldIH newIH t
    return ← withLocalDecl n bi t' fun x => do
      let ihs ← collectIHs is_wf fn oldIH newIH (body.instantiate1 x)
      ihs.mapM (mkLambdaFVars (usedOnly := true) #[x])

  | .lam n t body bi =>
    let t' ← foldCalls is_wf fn oldIH newIH t
    return ← withLocalDecl n bi t' fun x => do
      let ihs ← collectIHs is_wf fn oldIH newIH (body.instantiate1 x)
      ihs.mapM (mkLambdaFVars (usedOnly := true) #[x])

  | .mdata _m b =>
    return ← collectIHs is_wf fn oldIH newIH b

  | .sort .. | .lit .. | .const .. | .mvar .. | .bvar .. =>
    unreachable! -- cannot contain free variables, so early exit above kicks in

  | .fvar _ =>
    throwError "collectIHs: could not collect recursive calls, unsaturated application of old induction hypothesis"

-- Because of term duplications we might encounter the same IH multiple times.
-- We deduplicate them (by type, not proof term) here.
-- This could be improved and catch cases where the same IH is used in different contexts.
-- (Cf. `assignSubsumed` in `WF.Fix`)
def deduplicateIHs (vals : Array Expr) : MetaM (Array Expr) := do
  let mut vals' := #[]
  let mut types := #[]
  for v in vals do
    let t ← inferType v
    unless types.contains t do
      vals' := vals'.push v
      types := types.push t
  return vals'

def assertIHs (vals : Array Expr) (mvarid : MVarId) : MetaM MVarId := do
  let mut mvarid := mvarid
  for v in vals.reverse, i in [0:vals.size] do
    mvarid ← mvarid.assert (.mkSimple s!"ih{i+1}") (← inferType v) v
  return mvarid


/--
Substitutes equations, but makes sure to only substitute variables introduced after the motive
as the motive could depend on anything before, and `substVar` would happily drop equations
about these fixed parameters.
-/
def substVarAfter (mvarId : MVarId) (x : FVarId) : MetaM MVarId := do
  mvarId.withContext do
    let mut mvarId := mvarId
    let index := (← x.getDecl).index
    for localDecl in (← getLCtx) do
      if localDecl.index > index then
        mvarId ← trySubstVar mvarId localDecl.fvarId
    return mvarId

/--
Helper monad to traverse the function body, collecting the cases as mvars
-/
abbrev M α := StateT (Array MVarId) MetaM α


/-- Base case of `buildInductionBody`: Construct a case for the final induction hypthesis.  -/
def buildInductionCase (is_wf : Bool) (fn : Expr) (oldIH newIH : FVarId) (toClear toPreserve : Array FVarId)
    (goal : Expr) (IHs : Array Expr) (e : Expr) : M Expr := do
  let IHs := IHs ++ (← collectIHs is_wf fn oldIH newIH e)
  let IHs ← deduplicateIHs IHs

  let mvar ← mkFreshExprSyntheticOpaqueMVar goal (tag := `hyp)
  let mut mvarId := mvar.mvarId!
  mvarId ← assertIHs IHs mvarId
  for fvarId in toClear do
    mvarId ← mvarId.clear fvarId
  mvarId ← mvarId.cleanup (toPreserve := toPreserve)
  modify (·.push mvarId)
  let mvar ← instantiateMVars mvar
  pure mvar

/--
Like `mkLambdaFVars (usedOnly := true)`, but

 * silently skips expression in `xs` that are not `.isFVar`
 * returns a mask (same size as `xs`) indicating which variables have been abstracted
   (`true` means was abstracted).

The result `r` can be applied with `r.beta (maskArray mask args)`.

We use this when generating the functional induction principle to refine the goal through a `match`,
here `xs` are the discriminans of the `match`.
We do not expect non-trivial discriminants to appear in the goal (and if they do, the user will
get a helpful equality into the context).
-/
def mkLambdaFVarsMasked (xs : Array Expr) (e : Expr) : MetaM (Array Bool × Expr) := do
  let mut e := e
  let mut xs := xs
  let mut mask := #[]
  while ! xs.isEmpty do
    let discr := xs.back
    if discr.isFVar && e.containsFVar discr.fvarId! then
        e ← mkLambdaFVars #[discr] e
        mask := mask.push true
    else
        mask := mask.push false
    xs := xs.pop
  return (mask.reverse, e)

/-- `maskArray mask xs` keeps those `x` where the corresponding entry in `mask` is `true` -/
def maskArray {α} (mask : Array Bool) (xs : Array α) : Array α := Id.run do
  let mut ys := #[]
  for b in mask, x in xs do
    if b then ys := ys.push x
  return ys

/--
Builds an expression of type `goal` by replicating the expression `e` into its tail-call-positions,
where it calls `buildInductionCase`. Collects the cases of the final induction hypothesis
as `MVars` as it goes.
-/
partial def buildInductionBody (is_wf : Bool) (fn : Expr) (toClear toPreserve : Array FVarId)
    (goal : Expr) (oldIH newIH : FVarId) (IHs : Array Expr) (e : Expr) : M Expr := do
  -- logInfo m!"buildInductionBody {e}"

  -- if-then-else cause case split:
  match_expr e with
  | ite _α c h t f =>
    let IHs := IHs ++ (← collectIHs is_wf fn oldIH newIH c)
    let c' ← foldCalls is_wf fn oldIH newIH c
    let h' ← foldCalls is_wf fn oldIH newIH h
    let t' ← withLocalDecl `h .default c' fun h => do
      let t' ← buildInductionBody is_wf fn toClear (toPreserve.push h.fvarId!) goal oldIH newIH IHs t
      mkLambdaFVars #[h] t'
    let f' ← withLocalDecl `h .default (mkNot c') fun h => do
      let f' ← buildInductionBody is_wf fn toClear (toPreserve.push h.fvarId!) goal oldIH newIH IHs f
      mkLambdaFVars #[h] f'
    let u ← getLevel goal
    return mkApp5 (mkConst ``dite [u]) goal c' h' t' f'
  | dite _α c h t f =>
    let IHs := IHs ++ (← collectIHs is_wf fn oldIH newIH c)
    let c' ← foldCalls is_wf fn oldIH newIH c
    let h' ← foldCalls is_wf fn oldIH newIH h
    let t' ← withLocalDecl `h .default c' fun h => do
      let t ← instantiateLambda t #[h]
      let t' ← buildInductionBody is_wf fn toClear (toPreserve.push h.fvarId!) goal oldIH newIH IHs t
      mkLambdaFVars #[h] t'
    let f' ← withLocalDecl `h .default (mkNot c') fun h => do
      let f ← instantiateLambda f #[h]
      let f' ← buildInductionBody is_wf fn toClear (toPreserve.push h.fvarId!) goal oldIH newIH IHs f
      mkLambdaFVars #[h] f'
    let u ← getLevel goal
    return mkApp5 (mkConst ``dite [u]) goal c' h' t' f'
  | _ =>

  -- match and casesOn application cause case splitting
  if let some matcherApp ← matchMatcherApp? e (alsoCasesOn := true) then
    -- Collect IHs from the parameters and discrs of the matcher
    let paramsAndDiscrs := matcherApp.params ++ matcherApp.discrs
    let IHs := IHs ++ (← paramsAndDiscrs.concatMapM (collectIHs is_wf fn oldIH newIH ·))

    -- Calculate motive
    let eType ← newIH.getType
    let motiveBody ← mkArrow eType goal
    let (mask, absMotiveBody) ← mkLambdaFVarsMasked matcherApp.discrs motiveBody

    -- A match that refines the parameter has been modified by `Fix.lean` to refine the IH,
    -- so we need to replace that IH
    if matcherApp.remaining.size == 1 && matcherApp.remaining[0]!.isFVarOf oldIH then
      let matcherApp' ← matcherApp.transform (useSplitter := true)
        (addEqualities := mask.map not)
        (onParams := (foldCalls is_wf fn oldIH newIH ·))
        (onMotive := fun xs _body => pure (absMotiveBody.beta (maskArray mask xs)))
        (onAlt := fun expAltType alt => do
          removeLamda alt fun oldIH' alt => do
            forallBoundedTelescope expAltType (some 1) fun newIH' goal' => do
              let #[newIH'] := newIH' | unreachable!
              let alt' ← buildInductionBody is_wf fn (toClear.push newIH'.fvarId!) toPreserve goal' oldIH' newIH'.fvarId! IHs alt
              mkLambdaFVars #[newIH'] alt')
        (onRemaining := fun _ => pure #[.fvar newIH])
      return matcherApp'.toExpr

    -- A match that does not refine the parameter, but that we still want to split into separate
    -- cases
    if matcherApp.remaining.isEmpty then
      -- Calculate motive
      let (mask, absMotiveBody) ← mkLambdaFVarsMasked matcherApp.discrs goal

      let matcherApp' ← matcherApp.transform (useSplitter := true)
        (addEqualities := mask.map not)
        (onParams := (foldCalls is_wf fn oldIH newIH ·))
        (onMotive := fun xs _body => pure (absMotiveBody.beta (maskArray mask xs)))
        (onAlt := fun expAltType alt => do
          buildInductionBody is_wf fn toClear toPreserve expAltType oldIH newIH IHs alt)
      return matcherApp'.toExpr

  if let .letE n t v b _ := e then
    let IHs := IHs ++ (← collectIHs is_wf fn oldIH newIH v)
    let t' ← foldCalls is_wf fn oldIH newIH t
    let v' ← foldCalls is_wf fn oldIH newIH v
    return ← withLetDecl n t' v' fun x => do
      let b' ← buildInductionBody is_wf fn toClear toPreserve goal oldIH newIH IHs (b.instantiate1 x)
      mkLetFVars #[x] b'

  if let some (n, t, v, b) := e.letFun? then
    let IHs := IHs ++ (← collectIHs is_wf fn oldIH newIH v)
    let t' ← foldCalls is_wf fn oldIH newIH t
    let v' ← foldCalls is_wf fn oldIH newIH v
    return ← withLocalDecl n .default t' fun x => do
      let b' ← buildInductionBody is_wf fn toClear toPreserve goal oldIH newIH IHs (b.instantiate1 x)
      mkLetFun x v' b'

  liftM <| buildInductionCase is_wf fn oldIH newIH toClear toPreserve goal IHs e

/--
Given an expression `e` with metavariables
* collects all these meta-variables,
* lifts them to the current context by reverting all local declarations up to `x`
* introducing a local variable for each of the meta variable
* assigning that local variable to the mvar
* and finally lambda-abstracting over these new local variables.

This operation only works if the metavariables are independent from each other.

The resulting meta variable assignment is no longer valid (mentions out-of-scope
variables), so after this operations, terms that still mention these meta variables must not
be used anymore.

We are not using `mkLambdaFVars` on mvars directly, nor `abstractMVars`, as these at the moment
do not handle delayed assignemnts correctly.
-/
def abstractIndependentMVars (mvars : Array MVarId) (x : FVarId) (e : Expr) : MetaM Expr := do
  let mvars ← mvars.mapM fun mvar => do
    let mvar ← substVarAfter mvar x
    let (_, mvar) ← mvar.revertAfter x
    pure mvar
  let decls := mvars.mapIdx fun i mvar =>
    (.mkSimple s!"case{i.val+1}", .default, (fun _ => mvar.getType))
  Meta.withLocalDecls decls fun xs => do
      for mvar in mvars, x in xs do
        mvar.assign x
      mkLambdaFVars xs (← instantiateMVars e)

/-
Given a `brecOn` recursor, figures out which universe parameter has the motive.
Returns `none` if the the motive type is not of the form `… → Sort u`.
-/
def motiveUniverseParamPos (declName : Name) : MetaM (Option Nat) := do
  let info ← getConstInfo declName
  forallTelescopeReducing info.type fun _ type => do
    let motive  := type.getAppFn
    unless motive.isFVar do
      throwError "unexpected eliminator resulting type{indentExpr type}"
    let motiveType ← inferType motive
    forallTelescopeReducing motiveType fun _ motiveResultType => do
      match motiveResultType with
      | .sort (.param p) => return info.levelParams.toArray.indexOf? p
      | .sort _ => return none
      | _ => throwError "motive result type must be a sort{indentExpr motiveType}"

/--
This function looks that the body of a recursive function and looks for either users of
`fix`, `fixF` or a `.brecOn`, and abstracts over the differences between them. It passes
to the continuation

* whether we are using well-founded recursion
* the fixed parameters of the function body
* the varying parameters of the function body (this includes both the targets of the
  recursion and extra parameters passed to the recursor)
* the position of the motive/induction hypothesis in the body's arguments
* the body, as passed to the recursor. Expected to be a lambda that takes the
  varying parameters and the motive
* a function to re-assemble the call with a new Motive. The resulting expression expects
  the new body next, so that the expected type of the body can be inferred
* a function to finish assembling the call with the new body.
-/
def findRecursor {α} (name : Name) (varNames : Array Name) (e : Expr)
    (k :(is_wf : Bool) →
        (fixedParams : Array Expr) →
        (varyingParams : Array Expr) →
        (motivePosInBody : Nat) →
        (body : Expr) →
        (mkAppMotive : Expr → MetaM Expr) →
        (mkAppBody : Expr → Expr → Expr) →
        MetaM α) :
    MetaM α := do
  -- Uses of WellFounded.fix can be partially applied. Here we eta-expand the body
  -- to avoid dealing with this
  let e ← lambdaTelescope e fun params body => do mkLambdaFVars params (← etaExpand body)
  lambdaTelescope e fun params body => body.withApp fun f args => do
    MatcherApp.withUserNames params varNames do
      if not f.isConst then err else
      if isBRecOnRecursor (← getEnv) f.constName! then
        -- Bail out on mutual or nested inductives
        let .str indName _ := f.constName! | unreachable!
        let indInfo ← getConstInfoInduct indName
        if indInfo.all.length > 1 then
          throwError "functional induction: cannot handle mutual inductives"

        let elimInfo ← getElimExprInfo f
        let targets : Array Expr := elimInfo.targetsPos.map (args[·]!)
        let body := args[elimInfo.motivePos + 1 + elimInfo.targetsPos.size]!
        let extraArgs : Array Expr := args[elimInfo.motivePos + 1 + elimInfo.targetsPos.size + 1:]

        let fixedParams := params.filter fun x => !(targets.contains x || extraArgs.contains x)
        let varyingParams := params.filter fun x => targets.contains x || extraArgs.contains x
        unless params == fixedParams ++ varyingParams do
          throwError "functional induction: unexpected order of fixed and varying parameters:{indentExpr e}"
        unless 1 ≤ f.constLevels!.length do
          throwError "functional induction: unexpected recursor: {f} has no universe parameters"
        let value ←
          match (← motiveUniverseParamPos f.constName!) with
          | .some motiveUnivParam =>
            let us := f.constLevels!.set motiveUnivParam levelZero
            pure <| mkAppN (.const f.constName us) (args[:elimInfo.motivePos])
          | .none =>
            -- The `brecOn` does not support motives to any `Sort u`, so likely just `Type u`.
            -- Let's use `binductionOn` instead
            -- This code assumpes that `brecOn` has `u` first, and that the remaining universe
            -- parameters correspond
            let us := f.constLevels!.drop 1
            let bInductionName ← match f.constName with
              | .str indDeclName _ => pure <| mkBInductionOnName indDeclName
              | _ => throwError "Unexpected brecOn name {f.constName}"
            pure <| mkAppN (.const bInductionName us) (args[:elimInfo.motivePos])

        k false fixedParams varyingParams targets.size body
          (fun newMotive => do
            -- We may have to reorder the parameters for motive before passing it to brec
            let brecMotive ← mkLambdaFVars targets
              (← mkForallFVars extraArgs (mkAppN newMotive varyingParams))
            return mkAppN (mkApp value brecMotive) targets)
          (fun value newBody => mkAppN (.app value newBody) extraArgs)
      else if Name.isSuffixOf `brecOn f.constName! then
        throwError m!"Function {name} is defined in a way not supported by functional induction, " ++
          "for example by recursion over an inductive predicate."
      else match_expr body with
      | WellFounded.fixF α rel _motive body target acc =>
        unless params.back == target do
          throwError "functional induction: expected the target as last parameter{indentExpr e}"
        let value := .const ``WellFounded.fixF [f.constLevels![0]!, levelZero]
        k true params.pop #[params.back] 1 body
          (fun newMotive => pure (mkApp3 value α rel newMotive))
          (fun value newBody => mkApp2 value newBody acc)
      | WellFounded.fix α _motive rel wf body target =>
        unless params.back == target do
          throwError "functional induction: expected the target as last parameter{indentExpr e}"
        let value := .const ``WellFounded.fix [f.constLevels![0]!, levelZero]
        k true params.pop #[target] 1 body
          (fun newMotive => pure (mkApp4 value α newMotive rel wf))
          (fun value newBody => mkApp2 value newBody target)
      | _ => err
  where
    err := throwError m!"Function {name} does not look like a function defined by recursion." ++
      m!"\nNB: If {name} is not itself recursive, but contains an inner recursive " ++
      m!"function (via `let rec` or `where`), try `{name}.go` where `go` is name of the inner " ++
      "function."


/--
Given a definition `foo` defined via `WellFounded.fixF`, derive a suitable induction principle
`foo.induct` for it. See module doc for details.
 -/
def deriveUnaryInduction (name : Name) : MetaM Name := do
  let inductName := .append name `induct
  if ← hasConst inductName then return inductName

  let info ← getConstInfoDefn name

  let varNames ← forallTelescope info.type fun xs _ => xs.mapM (·.fvarId!.getUserName)

  let e' ← findRecursor name varNames info.value
    fun is_wf fixedParams varyingParams motivePosInBody body mkAppMotive mkAppBody => do
      let motiveType ← mkForallFVars varyingParams (.sort levelZero)
      withLocalDecl `motive .default motiveType fun motive => do
      let fn := mkAppN (.const name (info.levelParams.map mkLevelParam)) fixedParams
      let e' ← mkAppMotive motive
      check e'
      let (body', mvars) ← StateT.run (s := {}) do
        forallTelescope (← inferType e').bindingDomain! fun xs goal => do
          let arity := varyingParams.size + 1
          if xs.size ≠ arity then
            throwError "expected recursor argument to take {arity} parameters, got {xs}" else
          let targets : Array Expr := xs[:motivePosInBody]
          let genIH := xs[motivePosInBody]!
          let extraParams := xs[motivePosInBody+1:]
          -- open body with the same arg
          let body ← instantiateLambda body targets
          removeLamda body fun oldIH body => do
            let body ← instantiateLambda body extraParams
            let body' ← buildInductionBody is_wf fn #[genIH.fvarId!] #[] goal oldIH genIH.fvarId! #[] body
            if body'.containsFVar oldIH then
              throwError m!"Did not fully eliminate {mkFVar oldIH} from induction principle body:{indentExpr body}"
            mkLambdaFVars (targets.push genIH) (← mkLambdaFVars extraParams body')
      let e' := mkAppBody e' body'
      let e' ← mkLambdaFVars varyingParams e'
      let e' ← abstractIndependentMVars mvars motive.fvarId! e'
      let e' ← mkLambdaFVars #[motive] e'

      -- We could pass (usedOnly := true) below, and get nicer induction principles that
      -- do do not mention odd unused parameters.
      -- But the downside is that automatic instantiation of the principle (e.g. in a tactic
      -- that derives them from an function application in the goal) is harder, as
      -- one would have to infer or keep track of which parameters to pass.
      -- So for now lets just keep them around.
      let e' ← mkLambdaFVars (binderInfoForMVars := .default) fixedParams e'
      instantiateMVars e'

  unless (← isTypeCorrect e') do
    logError m!"failed to derive induction priciple:{indentExpr e'}"
    check e'

  let eTyp ← inferType e'
  let eTyp ← elimOptParam eTyp
  -- logInfo m!"eTyp: {eTyp}"
  let params := (collectLevelParams {} eTyp).params
  -- Prune unused level parameters, preserving the original order
  let us := info.levelParams.filter (params.contains ·)

  addDecl <| Declaration.thmDecl
    { name := inductName, levelParams := us, type := eTyp, value := e' }
  return inductName

/--
In the type of `value`, reduces
* Beta-redexes
* `PSigma.casesOn (PSigma.mk a b) (fun x y => k x y)  -->  k a b`
* `PSum.casesOn (PSum.inl x) k₁ k₂                    -->  k₁ x`
* `foo._unary (PSum.inl (PSigma.mk a b))              -->  foo a b`
and then wraps `value` in an appropriate type hint.
-/
def cleanPackedArgs (eqnInfo : WF.EqnInfo) (value : Expr) : MetaM Expr := do
  let t ← Meta.transform (← inferType value) (skipConstInApp := true) (pre := fun e => do
    -- Need to beta-reduce first
    let e' := e.headBeta
    if e' != e then
      return .visit e'
    -- Look for PSigma redexes
    if e.isAppOf ``PSigma.casesOn then
      let args := e.getAppArgs
      if 5 ≤ args.size then
        let scrut := args[3]!
        let k := args[4]!
        let extra := args[5:]
        if scrut.isAppOfArity ``PSigma.mk 4 then
          let #[_, _, x, y] := scrut.getAppArgs | unreachable!
          let e' := (k.beta #[x, y]).beta extra
          return .visit e'
    -- Look for PSum redexes
    if e.isAppOf ``PSum.casesOn then
      let args := e.getAppArgs
      if 6 ≤ args.size then
        let scrut := args[3]!
        let k₁ := args[4]!
        let k₂ := args[5]!
        let extra := args[6:]
        if scrut.isAppOfArity ``PSum.inl 3 then
          let e' := (k₁.beta #[scrut.appArg!]).beta extra
          return .visit e'
        if scrut.isAppOfArity ``PSum.inr 3 then
          let e' := (k₂.beta #[scrut.appArg!]).beta extra
          return .visit e'
    -- Look for _unary redexes
    if e.isAppOf eqnInfo.declNameNonRec then
      let args := e.getAppArgs
      if eqnInfo.fixedPrefixSize + 1 ≤ args.size then
        let packedArg := args.back
          let (i, unpackedArgs) ← eqnInfo.argsPacker.unpack packedArg
          let e' := .const eqnInfo.declNames[i]! e.getAppFn.constLevels!
          let e' := mkAppN e' args.pop
          let e' := mkAppN e' unpackedArgs
          let e' := mkAppN e' args[eqnInfo.fixedPrefixSize+1:]
          return .continue e'

    return .continue e)
  mkExpectedTypeHint value t

/--
Takes an induction principle where the motive is a `PSigma`/`PSum` type and
unpacks it into a n-ary and (possibly) joint induction principle.
-/
def unpackMutualInduction (eqnInfo : WF.EqnInfo) (unaryInductName : Name) : MetaM Name := do
  let inductName := if eqnInfo.declNames.size > 1 then
    .append eqnInfo.declNames[0]! `mutual_induct
  else
    -- If there is no mutual recursion, generate the `foo.induct` directly.
    .append eqnInfo.declNames[0]! `induct
  if ← hasConst inductName then return inductName

  let ci ← getConstInfo unaryInductName
  let us := ci.levelParams
  let value := .const ci.name (us.map mkLevelParam)
  let motivePos ← forallTelescope ci.type fun xs concl => concl.withApp fun motive targets => do
    unless motive.isFVar && targets.size = 1 && targets.all (·.isFVar) do
      throwError "conclusion {concl} does not look like a packed motive application"
    let packedTarget := targets[0]!
    unless xs.back == packedTarget do
      throwError "packed target not last argument to {unaryInductName}"
    let some motivePos := xs.findIdx? (· == motive)
      | throwError "could not find motive {motive} in {xs}"
    pure motivePos
  let value ← forallBoundedTelescope ci.type motivePos fun params type => do
    let value := mkAppN value params
    eqnInfo.argsPacker.curryParam value type fun motives value type =>
      -- Bring the rest into scope
      forallTelescope type fun xs _concl => do
        let alts := xs.pop
        let value := mkAppN value alts
        let value ← eqnInfo.argsPacker.curry value
        let value ← mkLambdaFVars alts value
        let value ← mkLambdaFVars motives value
        let value ← mkLambdaFVars params value
        check value
        let value ← cleanPackedArgs eqnInfo value
        return value

  unless ← isTypeCorrect value do
    logError m!"failed to unpack induction priciple:{indentExpr value}"
    check value
  let type ← inferType value
  let type ← elimOptParam type

  addDecl <| Declaration.thmDecl
    { name := inductName, levelParams := ci.levelParams, type, value }
  return inductName

/-- Given `foo._unary.induct`, define `foo.mutual_induct` and then `foo.induct`, `bar.induct`, … -/
def deriveUnpackedInduction (eqnInfo : WF.EqnInfo) (unaryInductName : Name): MetaM Unit := do
  let unpackedInductName ← unpackMutualInduction eqnInfo unaryInductName
  let ci ← getConstInfo unpackedInductName
  let levelParams := ci.levelParams

  for name in eqnInfo.declNames, idx in [:eqnInfo.declNames.size] do
    let inductName := .append name `induct
    unless ← hasConst inductName do
      let value ← forallTelescope ci.type fun xs _body => do
        let value := .const ci.name (levelParams.map mkLevelParam)
        let value := mkAppN value xs
        let value := mkProjAndN eqnInfo.declNames.size idx value
        mkLambdaFVars xs value
      let type ← inferType value
      addDecl <| Declaration.thmDecl { name := inductName, levelParams, type, value }

/--
Given a recursively defined function `foo`, derives `foo.induct`. See the module doc for details.
-/
def deriveInduction (name : Name) : MetaM Unit := do
  if let some eqnInfo := WF.eqnInfoExt.find? (← getEnv) name then
    let unaryInductName ← deriveUnaryInduction eqnInfo.declNameNonRec
    unless eqnInfo.declNameNonRec = name do
      deriveUnpackedInduction eqnInfo unaryInductName
  else
    _ ← deriveUnaryInduction name

def isFunInductName (env : Environment) (name : Name) : Bool := Id.run do
  let .str p s := name | return false
  match s with
  | "induct" =>
    if (WF.eqnInfoExt.find? env p).isSome then return true
    if (Structural.eqnInfoExt.find? env p).isSome then return true
    return false
  | "mutual_induct" =>
    if let some eqnInfo := WF.eqnInfoExt.find? env p then
      if h : eqnInfo.declNames.size > 1 then
        return eqnInfo.declNames[0] = p
    return false
  | _ => return false

builtin_initialize
  registerReservedNamePredicate isFunInductName

  registerReservedNameAction fun name => do
    if isFunInductName (← getEnv) name then
      let .str p _ := name | return false
      MetaM.run' <| deriveInduction p
      return true
    return false

end Lean.Tactic.FunInd
