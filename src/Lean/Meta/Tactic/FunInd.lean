/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

prelude
import Lean.Meta.Basic
import Lean.Meta.Match.MatcherApp.Transform
import Lean.Meta.Check
import Lean.Meta.Tactic.Subst
import Lean.Meta.Injective -- for elimOptParam
import Lean.Meta.ArgsPacker
import Lean.Meta.PProdN
import Lean.Elab.PreDefinition.WF.Eqns
import Lean.Elab.PreDefinition.Structural.Eqns
import Lean.Elab.PreDefinition.Structural.IndGroupInfo
import Lean.Elab.PreDefinition.Structural.FindRecArg
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
depend on the bound values, then these become assumptions of the inductive
hypothesis.

Additionally, the local context of the branch (e.g. the condition of an
if-then-else; a let-binding, a have-binding) is provided as assumptions in the
corresponding induction case, if they are likely to be useful (as determined
by `MVarId.cleanup`).

Mutual recursion is supported and results in multiple motives.


## Implementation overview (well-founded recursion)

For a non-mutual, unary function `foo` (or else for the `_unary` function), we

1. expect its definition to be of the form
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

3. The first phase, transformation `T1[body]` (implemented in `buildInductionBody`)
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
     patterns are overlapping (using `matcherApp.transform (useSplitter := true)`)
   * simple discriminants that are mentioned in the goal (i.e plain parameters) are instantiated
     in the goal.
   * for discriminants that are not instantiated that way, equalities connecting the discriminant
     to the instantiation are added (just as if the user wrote `match h : x with …`)

4. When a tail position (no more branching) is found, function `buildInductionCase` assembles the
   type of the case: a fresh `MVar` asserts the current goal, unwanted values from the local context
   are cleared, and the current `body` is searched for recursive calls using `foldAndCollect`,
   which are then asserted as inductive hyptheses in the `MVar`.

5. The function `foldAndCollect` walks the term and performs two operations:

   * collects the induction hypotheses for the current case (with proofs).
   * recovering the recursive calls

   So when it encounters a saturated application of `oldIH arg proof`, it
   * returns `f arg` and
   * remembers the expression `newIH arg proof : motive x` as an inductive hypothesis.

   Since `arg` and `proof` can contain further recursive calls, they are folded there as well.
   This assumes that the termination proof `proof` works nevertheless.

   Again, `foldAndCollect` may encounter the `Lean.Meta.Matcherapp.addArg?` idiom, and again it
   threads `newIH` through, replacing the extra argument. The resulting type of this induction
   hypothesis is now itself a `match` statement (cf. `Lean.Meta.MatcherApp.inferMatchType`)

   The termination proof of `foo` may have abstracted over some proofs; these proofs must be
   transferred, so auxiliary lemmas are unfolded if needed.

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

Finally, in `deriveUnpackedInduction`, for each of the functions in the mutual group, a simple
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

  Since (for now) we only support `Prop` in the induction principle, we rewrite to `.binductionOn`.

* The elaboration of structurally recursive function can handle extra arguments. We keep the
  `motive` parameters in the original order.
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


/--
A monad to help collecting inductive hypothesis.

In `foldAndCollect` it's a writer monad (with variants of the `local` combinator),
and in `buildInductionBody` it is more of a reader monad, with inductive hypotheses
being passed down (hence the `ask` and `branch` combinator).
-/
abbrev M := StateT (Array Expr) MetaM

namespace M

variable {α : Type}

def run (act : M α) : MetaM (α × Array Expr) := StateT.run act #[]
def eval (act : M α) : MetaM α := do return (← run act).1
def exec (act : M α) : MetaM (Array Expr) := do return (← run act).2

def tell (x : Expr) : M Unit := fun xs => pure ((), xs.push x)

def localM (f : Array Expr → MetaM (Array Expr)) (act : M α) : M α := fun xs => do
  let n := xs.size
  let (b, xs') ← act xs
  pure (b, xs'[:n] ++ (← f xs'[n:]))

def localMapM (f : Expr → MetaM Expr) (act : M α) : M α :=
  localM (·.mapM f) act

def ask : M (Array Expr) := get

def branch (act : M α) : M α :=
  localM (fun _ => pure #[]) act

end M

/--
The `foldAndCollect` function performs two operations together:

 * it fold recursive calls: applications (and projectsions) of `oldIH` in `e` correspond to
   recursive calls, so this function rewrites that back to recursive calls
 * it collects induction hypotheses: after replacing `oldIH` with `newIH`, applications thereof
   are valuable as induction hypotheses for the cases.

For well-founded recursion (unary, non-mutual by construction) the terms are rather simple: they
are `oldIH arg proof`, and can be rewritten to `f arg` resp. `newIH arg proof`. But for
structural recursion this can be a more complicted mix of function applications (due to reflexive
data types or extra function arguments) and `PProd` projections (due to the below construction and
mutual function packing), and the main function argument isn't even present.

To avoid having to think about this, we apply a nice trick:

We compositionally replace `oldIH` with `newIH`. This likely changes the result type, so when
re-assembling we have to be supple (mainly around `PProd.fst`/`PProd.snd`). As we re-assemble
the term we check if it has type `motive xs..`. If it has, then know we have just found and
rewritten a recursive call, and this type nicely provides us the arguments `xs`. So at this point
we store the rewritten expression as a new induction hypothesis (using `M.tell`) and rewrite to
`f xs..`, which now again has the same type as the original term, and the further re-assembly should
work. Half this logic is in the `isRecCall` parameter.

If this process fails we’ll get weird type errors (caught later on). We'll see if we need to
improve the errors, for example by passing down a flag whether we expect the same type (and no
occurrences of `newIH`), or whether we are in “supple mode”, and catch it earlier if the rewriting
fails.
-/
partial def foldAndCollect (oldIH newIH : FVarId) (isRecCall : Expr → Option Expr) (e : Expr) : M Expr := do
  unless e.containsFVar oldIH do
    return e

  let e' ← id do
    if let some (n, t, v, b) := e.letFun? then
      let t' ← foldAndCollect oldIH newIH isRecCall t
      let v' ← foldAndCollect oldIH newIH isRecCall v
      return ← withLocalDeclD n t' fun x => do
        M.localMapM (mkLetFun x v' ·) do
          let b' ← foldAndCollect oldIH newIH isRecCall (b.instantiate1 x)
          mkLetFun x v' b'

    if let some matcherApp ← matchMatcherApp? e (alsoCasesOn := true) then
      if matcherApp.remaining.size == 1 && matcherApp.remaining[0]!.isFVarOf oldIH then
        -- We do different things to the matcher when folding recursive calls and when
        -- collecting inductive hypotheses. Therefore we do it separately,
        -- droppin got `MetaM` in between, and using `M.eval`/`M.exec` as appropriate
        -- We could try to do it in one pass by breaking up the `matcherApp.transform`
        -- abstraction.

        -- To collect the IHs, we collect them in each branch, and combine
        -- them to a type-leve match
        let ihMatcherApp' ← liftM <| matcherApp.transform
          (onParams := fun e => M.eval <| foldAndCollect oldIH newIH isRecCall e)
          (onMotive := fun xs _body => do
            -- Remove the old IH that was added in mkFix
            let eType ← newIH.getType
            let eTypeAbst ← matcherApp.discrs.size.foldRevM (init := eType) fun i eTypeAbst => do
              let motiveArg := xs[i]!
              let discr     := matcherApp.discrs[i]!
              let eTypeAbst ← kabstract eTypeAbst discr
              return eTypeAbst.instantiate1 motiveArg

            -- Will later be overridden with a type that’s itself a match
            -- statement and the inferred alt types
            let dummyGoal := mkConst ``True []
            mkArrow eTypeAbst dummyGoal)
          (onAlt := fun altType alt => do
            removeLamda alt fun oldIH' alt => do
              forallBoundedTelescope altType (some 1) fun newIH' _goal' => do
                let #[newIH'] := newIH' | unreachable!
                let altIHs ← M.exec <| foldAndCollect oldIH' newIH'.fvarId! isRecCall alt
                let altIH ← PProdN.mk 0 altIHs
                mkLambdaFVars #[newIH'] altIH)
          (onRemaining := fun _ => pure #[mkFVar newIH])
        let ihMatcherApp'' ← ihMatcherApp'.inferMatchType
        M.tell ihMatcherApp''.toExpr

        -- Folding the calls is straight forward
        let matcherApp' ← liftM <| matcherApp.transform
          (onParams := fun e => M.eval <| foldAndCollect oldIH newIH isRecCall e)
          (onMotive := fun _motiveArgs motiveBody => do
            let some (_extra, body) := motiveBody.arrow? | throwError "motive not an arrow"
            M.eval (foldAndCollect oldIH newIH isRecCall body))
          (onAlt := fun _altType alt => do
            removeLamda alt fun oldIH alt => do
              M.eval (foldAndCollect oldIH newIH isRecCall alt))
          (onRemaining := fun _ => pure #[])
        return matcherApp'.toExpr


    if e.getAppArgs.any (·.isFVarOf oldIH) then
      -- Sometimes Fix.lean abstracts over oldIH in a proof definition.
      -- So beta-reduce that definition. We need to look through theorems here!
      let e' ← withTransparency .all do whnf e
      if e == e' then
        throwError "foldAndCollect: cannot reduce application of {e.getAppFn} in:{indentExpr e} "
      return ← foldAndCollect oldIH newIH isRecCall e'

    match e with
    | .app e1 e2 =>
      pure <|.app (← foldAndCollect oldIH newIH isRecCall e1) (← foldAndCollect oldIH newIH isRecCall e2)

    | .lam n t body bi =>
      let t' ← foldAndCollect oldIH newIH isRecCall t
      withLocalDecl n bi t' fun x => do
        M.localMapM (mkLambdaFVars (usedOnly := true) #[x] ·) do
          let body' ← foldAndCollect oldIH newIH isRecCall (body.instantiate1 x)
          mkLambdaFVars #[x] body'

    | .forallE n t body bi =>
      let t' ← foldAndCollect oldIH newIH isRecCall t
      withLocalDecl n bi t' fun x => do
        M.localMapM (mkLambdaFVars (usedOnly := true) #[x] ·) do
          let body' ← foldAndCollect oldIH newIH isRecCall (body.instantiate1 x)
          mkForallFVars #[x] body'

    | .letE n t v b _ =>
      let t' ← foldAndCollect oldIH newIH isRecCall t
      let v' ← foldAndCollect oldIH newIH isRecCall v
      withLetDecl n t' v' fun x => do
        M.localMapM (mkLetFVars (usedLetOnly := true) #[x] ·) do
          let b' ← foldAndCollect oldIH newIH isRecCall (b.instantiate1 x)
          mkLetFVars #[x] b'

    | .mdata m b =>
      pure <| .mdata m (← foldAndCollect oldIH newIH isRecCall b)

    -- These projections can be type changing (to And), so re-infer their type arguments
    | .proj ``PProd 0 e => mkPProdFst (← foldAndCollect oldIH newIH isRecCall e)
    | .proj ``PProd 1 e => mkPProdSnd (← foldAndCollect oldIH newIH isRecCall e)

    | .proj t i e =>
      pure <| .proj t i (← foldAndCollect oldIH newIH isRecCall e)

    | .sort .. | .lit .. | .const .. | .mvar .. | .bvar .. =>
      unreachable! -- cannot contain free variables, so early exit above kicks in

    | .fvar fvar =>
      assert! fvar == oldIH
      pure <| mkFVar newIH

    -- Now see if the type o/--f the expression we are building is a motive application.
    -- If it is we want to replace it with the corresponding function application,
    -- and remember the expression as a IH to be used in an inductive case.

  if e'.containsFVar oldIH then
    throwError "Failed to eliminate {mkFVar oldIH} from:{indentExpr e'}"

  let eType ← whnf (← inferType e')
  if let .some call := isRecCall eType then
    M.tell (← mkExpectedTypeHint e' eType)
    return call

  return e'

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
Goal cleanup:
Substitutes equations (with `substVar`) to remove superfluous variables, and clears unused
let bindings.

Substitutes from the outside in so that the inner-bound variable name wins, but does a first pass
looking only at variables with names with macro scope, so that preferably they disappear.

Careful to only touch the context after the motives (given by the index) as the motive could depend
on anything before, and `substVar` would happily drop equations about these fixed parameters.
-/
partial def cleanupAfter (mvarId : MVarId) (index : Nat) : MetaM MVarId := do
  let mvarId ← go mvarId index true
  let mvarId ← go mvarId index false
  return mvarId
where
  go (mvarId : MVarId) (index : Nat) (firstPass : Bool) : MetaM MVarId := do
    if let some mvarId ← cleanupAfter? mvarId index firstPass then
      go mvarId index firstPass
    else
      return mvarId

  allHeqToEq (mvarId : MVarId) (index : Nat) : MetaM MVarId :=
    mvarId.withContext do
      let mut mvarId := mvarId
      for localDecl in (← getLCtx) do
        if localDecl.index > index then
          let (_, mvarId') ← heqToEq mvarId localDecl.fvarId
          mvarId := mvarId'
      return mvarId

  cleanupAfter? (mvarId : MVarId) (index : Nat) (firstPass : Bool)  : MetaM (Option MVarId) := do
    mvarId.withContext do
      for localDecl in (← getLCtx) do
        if localDecl.index > index && (!firstPass || localDecl.userName.hasMacroScopes) then
          if localDecl.isLet then
            if let some mvarId' ← observing? <| mvarId.clear localDecl.fvarId then
              return some mvarId'
          if let some mvarId' ← substVar? mvarId localDecl.fvarId then
            -- After substituting, some HEq might turn into Eqs, and we want to be able to substitute
            -- them as well
            let mvarId' ← allHeqToEq mvarId' index
            return some mvarId'
      return none


/--
Second helper monad collecting the cases as mvars
-/
abbrev M2 α := StateT (Array MVarId) M α

def M2.run {α} (act : M2 α) : MetaM (α × Array MVarId) :=
  M.eval (StateT.run (s := #[]) act)

def M2.branch {α} (act : M2 α) : M2 α :=
  controlAt M fun runInBase => M.branch (runInBase act)


/-- Base case of `buildInductionBody`: Construct a case for the final induction hypthesis.  -/
def buildInductionCase (oldIH newIH : FVarId) (isRecCall : Expr → Option Expr) (toClear : Array FVarId)
    (goal : Expr)  (e : Expr) : M2 Expr := do
  let _e' ← foldAndCollect oldIH newIH isRecCall e
  let IHs : Array Expr ← M.ask
  let IHs ← deduplicateIHs IHs

  let mvar ← mkFreshExprSyntheticOpaqueMVar goal (tag := `hyp)
  let mut mvarId := mvar.mvarId!
  mvarId ← assertIHs IHs mvarId
  trace[Meta.FunInd] "Goal before cleanup:{mvarId}"
  for fvarId in toClear do
    mvarId ← mvarId.clear fvarId
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
here `xs` are the discriminants of the `match`.
We do not expect non-trivial discriminants to appear in the goal (and if they do, the user will
get a helpful equality into the context).
-/
def mkLambdaFVarsMasked (xs : Array Expr) (e : Expr) : MetaM (Array Bool × Expr) := do
  let mut e := e
  let mut xs := xs
  let mut mask := #[]
  while !xs.isEmpty do
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
partial def buildInductionBody (toClear : Array FVarId) (goal : Expr)
    (oldIH newIH : FVarId) (isRecCall : Expr → Option Expr) (e : Expr) : M2 Expr := do

  -- if-then-else cause case split:
  match_expr e with
  | ite _α c h t f =>
    let c' ← foldAndCollect oldIH newIH isRecCall c
    let h' ← foldAndCollect oldIH newIH isRecCall h
    let t' ← withLocalDecl `h .default c' fun h => M2.branch do
      let t' ← buildInductionBody toClear goal oldIH newIH isRecCall t
      mkLambdaFVars #[h] t'
    let f' ← withLocalDecl `h .default (mkNot c') fun h => M2.branch do
      let f' ← buildInductionBody toClear goal oldIH newIH isRecCall f
      mkLambdaFVars #[h] f'
    let u ← getLevel goal
    return mkApp5 (mkConst ``dite [u]) goal c' h' t' f'
  | dite _α c h t f =>
    let c' ← foldAndCollect oldIH newIH isRecCall c
    let h' ← foldAndCollect oldIH newIH isRecCall h
    let t' ← withLocalDecl `h .default c' fun h => M2.branch do
      let t ← instantiateLambda t #[h]
      let t' ← buildInductionBody toClear goal oldIH newIH isRecCall t
      mkLambdaFVars #[h] t'
    let f' ← withLocalDecl `h .default (mkNot c') fun h => M2.branch do
      let f ← instantiateLambda f #[h]
      let f' ← buildInductionBody toClear goal oldIH newIH isRecCall f
      mkLambdaFVars #[h] f'
    let u ← getLevel goal
    return mkApp5 (mkConst ``dite [u]) goal c' h' t' f'

  | _ =>

  -- we look in to `PProd.mk`, as it occurs in the mutual structural recursion construction
  match_expr goal with
  | And goal₁ goal₂ => match_expr e with
    | PProd.mk _α _β e₁ e₂ =>
      let e₁' ← buildInductionBody toClear goal₁ oldIH newIH isRecCall e₁
      let e₂' ← buildInductionBody toClear goal₂ oldIH newIH isRecCall e₂
      return mkApp4 (.const ``And.intro []) goal₁ goal₂ e₁' e₂'
    | _ =>
      throwError "Goal is PProd, but expression is:{indentExpr e}"
  | True =>
    return .const ``True.intro []
  | _ =>

  -- match and casesOn application cause case splitting
  if let some matcherApp ← matchMatcherApp? e (alsoCasesOn := true) then
    -- Calculate motive
    let eType ← newIH.getType
    let motiveBody ← mkArrow eType goal
    let (mask, absMotiveBody) ← mkLambdaFVarsMasked matcherApp.discrs motiveBody

    -- A match that refines the parameter has been modified by `Fix.lean` to refine the IH,
    -- so we need to replace that IH
    if matcherApp.remaining.size == 1 && matcherApp.remaining[0]!.isFVarOf oldIH then
      let matcherApp' ← matcherApp.transform (useSplitter := true)
        (addEqualities := true)
        (onParams := (foldAndCollect oldIH newIH isRecCall ·))
        (onMotive := fun xs _body => pure (absMotiveBody.beta (maskArray mask xs)))
        (onAlt := fun expAltType alt => M2.branch do
          removeLamda alt fun oldIH' alt => do
            forallBoundedTelescope expAltType (some 1) fun newIH' goal' => do
              let #[newIH'] := newIH' | unreachable!
              let alt' ← buildInductionBody (toClear.push newIH'.fvarId!) goal' oldIH' newIH'.fvarId! isRecCall alt
              mkLambdaFVars #[newIH'] alt')
        (onRemaining := fun _ => pure #[.fvar newIH])
      return matcherApp'.toExpr

    -- A match that does not refine the parameter, but that we still want to split into separate
    -- cases
    if matcherApp.remaining.isEmpty then
      -- Calculate motive
      let (mask, absMotiveBody) ← mkLambdaFVarsMasked matcherApp.discrs goal

      let matcherApp' ← matcherApp.transform (useSplitter := true)
        (addEqualities := true)
        (onParams := (foldAndCollect oldIH newIH isRecCall ·))
        (onMotive := fun xs _body => pure (absMotiveBody.beta (maskArray mask xs)))
        (onAlt := fun expAltType alt => M2.branch do
          buildInductionBody toClear expAltType oldIH newIH isRecCall alt)
      return matcherApp'.toExpr

  -- we look through mdata
  if e.isMData then
    let b ← buildInductionBody toClear goal oldIH newIH isRecCall e.mdataExpr!
    return e.updateMData! b

  if let .letE n t v b _ := e then
    let t' ← foldAndCollect oldIH newIH isRecCall t
    let v' ← foldAndCollect oldIH newIH isRecCall v
    return ← withLetDecl n t' v' fun x => M2.branch do
      let b' ← buildInductionBody toClear goal oldIH newIH isRecCall (b.instantiate1 x)
      mkLetFVars #[x] b'

  if let some (n, t, v, b) := e.letFun? then
    let t' ← foldAndCollect oldIH newIH isRecCall t
    let v' ← foldAndCollect oldIH newIH isRecCall v
    return ← withLocalDeclD n t' fun x => M2.branch do
      let b' ← buildInductionBody toClear goal oldIH newIH isRecCall (b.instantiate1 x)
      mkLetFun x v' b'

  liftM <| buildInductionCase oldIH newIH isRecCall toClear goal e

/--
Given an expression `e` with metavariables `mvars`
* performs more cleanup:
  * removes unused let-expressions after index `index`
  * tries to substitute variables after index `index`
* lifts them to the current context by reverting all local declarations after index `index`
* introducing a local variable for each of the meta variable
* assigning that local variable to the mvar
* and finally lambda-abstracting over these new local variables.

This operation only works if the metavariables are independent from each other.

The resulting meta variable assignment is no longer valid (mentions out-of-scope
variables), so after this operations, terms that still mention these meta variables must not
be used anymore.

We are not using `mkLambdaFVars` on mvars directly, nor `abstractMVars`, as these at the moment
do not handle delayed assignments correctly.
-/
def abstractIndependentMVars (mvars : Array MVarId) (index : Nat) (e : Expr) : MetaM Expr := do
  trace[Meta.FunInd] "abstractIndependentMVars, to revert after {index}, original mvars: {mvars}"
  let mvars ← mvars.mapM fun mvar => do
    let mvar ← cleanupAfter mvar index
    mvar.withContext do
      let fvarIds := (← getLCtx).foldl (init := #[]) (start := index+1) fun fvarIds decl => fvarIds.push decl.fvarId
      let (_, mvar) ← mvar.revert fvarIds
      pure mvar
  trace[Meta.FunInd] "abstractIndependentMVars, reverted mvars: {mvars}"
  let decls := mvars.mapIdx fun i mvar =>
    (.mkSimple s!"case{i+1}", (fun _ => mvar.getType))
  Meta.withLocalDeclsD decls fun xs => do
      for mvar in mvars, x in xs do
        mvar.assign x
      mkLambdaFVars xs (← instantiateMVars e)

/--
Given a unary definition `foo` defined via `WellFounded.fixF`, derive a suitable induction principle
`foo.induct` for it. See module doc for details.
 -/
def deriveUnaryInduction (name : Name) : MetaM Name := do
  let inductName := .append name `induct
  if ← hasConst inductName then return inductName

  let info ← getConstInfoDefn name

  let varNames ← forallTelescope info.type fun xs _ => xs.mapM (·.fvarId!.getUserName)

  -- Uses of WellFounded.fix can be partially applied. Here we eta-expand the body
  -- to make sure that `target` indeed the last parameter
  let e := info.value
  let e ← lambdaTelescope e fun params body => do
    if body.isAppOfArity ``WellFounded.fix 5 then
      forallBoundedTelescope (← inferType body) (some 1) fun xs _ => do
        unless xs.size = 1 do
          throwError "functional induction: Failed to eta-expand{indentExpr e}"
        mkLambdaFVars (params ++ xs) (mkAppN body xs)
    else
      pure e
  let e' ← lambdaTelescope e fun params funBody => MatcherApp.withUserNames params varNames do
    match_expr funBody with
    | fix@WellFounded.fix α _motive rel wf body target =>
      unless params.back == target do
        throwError "functional induction: expected the target as last parameter{indentExpr e}"
      let fixedParams := params.pop
      let motiveType ← mkForallFVars #[target] (.sort levelZero)
      withLocalDeclD `motive motiveType fun motive => do
        let fn := mkAppN (← mkConstWithLevelParams name) fixedParams
        let isRecCall : Expr → Option Expr := fun e =>
          if e.isApp && e.appFn!.isFVarOf motive.fvarId! then
            mkApp fn e.appArg!
          else
            none

        let e' := .const ``WellFounded.fix [fix.constLevels![0]!, levelZero]
        let e' := mkApp4 e' α motive rel wf
        check e'
        let (body', mvars) ← M2.run do
          forallTelescope (← inferType e').bindingDomain! fun xs goal => do
            if xs.size ≠ 2 then
              throwError "expected recursor argument to take 2 parameters, got {xs}" else
            let targets : Array Expr := xs[:1]
            let genIH := xs[1]!
            let extraParams := xs[2:]
            -- open body with the same arg
            let body ← instantiateLambda body targets
            removeLamda body fun oldIH body => do
              let body ← instantiateLambda body extraParams
              let body' ← buildInductionBody #[genIH.fvarId!] goal oldIH genIH.fvarId! isRecCall body
              if body'.containsFVar oldIH then
                throwError m!"Did not fully eliminate {mkFVar oldIH} from induction principle body:{indentExpr body}"
              mkLambdaFVars (targets.push genIH) (← mkLambdaFVars extraParams body')
        let e' := mkApp2 e' body' target
        let e' ← mkLambdaFVars #[target] e'
        let e' ← abstractIndependentMVars mvars (← motive.fvarId!.getDecl).index e'
        let e' ← mkLambdaFVars #[motive] e'

        -- We could pass (usedOnly := true) below, and get nicer induction principles that
        -- do not mention odd unused parameters.
        -- But the downside is that automatic instantiation of the principle (e.g. in a tactic
        -- that derives them from an function application in the goal) is harder, as
        -- one would have to infer or keep track of which parameters to pass.
        -- So for now lets just keep them around.
        let e' ← mkLambdaFVars (binderInfoForMVars := .default) fixedParams e'
        instantiateMVars e'
    | _ =>
      if funBody.isAppOf ``WellFounded.fix then
        throwError "Function {name} defined via WellFounded.fix with unexpected arity {funBody.getAppNumArgs}:{indentExpr funBody}"
      else
        throwError "Function {name} not defined via WellFounded.fix:{indentExpr funBody}"

  unless (← isTypeCorrect e') do
    logError m!"failed to derive a type-correct induction principle:{indentExpr e'}"
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
Given `foo.mutual_induct`, defined `foo.induct`, `bar.induct` etc.
Used for well-founded and structural recursion.
-/
def projectMutualInduct (names : Array Name) (mutualInduct : Name) : MetaM Unit := do
  let ci ← getConstInfo mutualInduct
  let levelParams := ci.levelParams

  for name in names, idx in [:names.size] do
    let inductName := .append name `induct
    unless ← hasConst inductName do
      let value ← forallTelescope ci.type fun xs _body => do
        let value := .const ci.name (levelParams.map mkLevelParam)
        let value := mkAppN value xs
        let value ← PProdN.proj names.size idx value
        mkLambdaFVars xs value
      let type ← inferType value
      addDecl <| Declaration.thmDecl { name := inductName, levelParams, type, value }

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
Takes `foo._unary.induct`, where the motive is a `PSigma`/`PSum` type and
unpacks it into a n-ary and (possibly) joint induction principle.
-/
def unpackMutualInduction (eqnInfo : WF.EqnInfo) (unaryInductName : Name) : MetaM Name := do
  let inductName := if eqnInfo.declNames.size > 1 then
    .append eqnInfo.declNames[0]! `mutual_induct
  else
    -- If there is no mutual recursion, we generate the `foo.induct` directly.
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
    logError m!"failed to unpack induction principle:{indentExpr value}"
    check value
  let type ← inferType value
  let type ← elimOptParam type

  addDecl <| Declaration.thmDecl
    { name := inductName, levelParams := ci.levelParams, type, value }
  return inductName


/-- Given `foo._unary.induct`, define `foo.mutual_induct` and then `foo.induct`, `bar.induct`, … -/
def deriveUnpackedInduction (eqnInfo : WF.EqnInfo) (unaryInductName : Name): MetaM Unit := do
  let unpackedInductName ← unpackMutualInduction eqnInfo unaryInductName
  projectMutualInduct eqnInfo.declNames unpackedInductName

def stripPProdProjs (e : Expr) : Expr :=
  match e with
  | .proj ``PProd _ e' => stripPProdProjs e'
  | .proj ``And _ e' => stripPProdProjs e'
  | e => e

def withLetDecls {α} (name : Name) (ts : Array Expr) (es : Array Expr) (k : Array Expr → MetaM α) : MetaM α := do
  assert! es.size = ts.size
  go 0 #[]
where
  go (i : Nat) (acc : Array Expr) := do
    if h : i < es.size then
      let n := if es.size = 1 then name else name.appendIndexAfter (i + 1)
      withLetDecl n ts[i]! es[i] fun x => go (i+1) (acc.push x)
    else
      k acc

/--
Given a recursive definition `foo` defined via structural recursion, derive `foo.mutual_induct`,
if needed, and `foo.induct` for all functions in the group.
See module doc for details.
 -/
def deriveInductionStructural (names : Array Name) (numFixed : Nat) : MetaM Unit := do
  let infos ← names.mapM getConstInfoDefn
  -- First open up the fixed parameters everywhere
  let e' ← lambdaBoundedTelescope infos[0]!.value numFixed fun xs _ => do
    -- Now look at the body of an arbitrary of the functions (they are essentially the same
    -- up to the final projections)
    let body ← instantiateLambda infos[0]!.value xs

    lambdaTelescope body fun ys body => do
      -- The body is of the form (brecOn … ).2.2.1 extra1 extra2 etc; ignore the
      -- projection here
      let f' := body.getAppFn
      let body' := stripPProdProjs f'
      let f := body'.getAppFn
      let args := body'.getAppArgs ++ body.getAppArgs

      let body := stripPProdProjs body
      let .const brecOnName us := f |
        throwError "{infos[0]!.name}: unexpected body:{indentExpr infos[0]!.value}"
      unless isBRecOnRecursor (← getEnv) brecOnName do
        throwError "{infos[0]!.name}: expected .brecOn application, found:{indentExpr body}"

      let .str indName _ := brecOnName | unreachable!
      let indInfo ← getConstInfoInduct indName

      -- we have a `.brecOn` application, so now figure out the length of the fixed prefix
      -- we can use the recInfo for `.rec`, since `.brecOn` has a similar structure
      let recInfo ← getConstInfoRec (mkRecName indName)
      if args.size < recInfo.numParams + recInfo.numMotives + recInfo.numIndices + 1 + recInfo.numMotives then
        throwError "insufficient arguments to .brecOn:{indentExpr body}"
      let brecOnArgs    : Array Expr := args[:recInfo.numParams]
      let _brecOnMotives : Array Expr := args[recInfo.numParams:recInfo.numParams + recInfo.numMotives]
      let brecOnTargets : Array Expr := args[recInfo.numParams + recInfo.numMotives :
        recInfo.numParams + recInfo.numMotives + recInfo.numIndices + 1]
      let brecOnMinors  : Array Expr := args[recInfo.numParams + recInfo.numMotives + recInfo.numIndices + 1 :
        recInfo.numParams + recInfo.numMotives + recInfo.numIndices + 1 + recInfo.numMotives]
      let brecOnExtras  : Array Expr := args[ recInfo.numParams + recInfo.numMotives + recInfo.numIndices + 1 +
        recInfo.numMotives:]
      unless brecOnTargets.all (·.isFVar) do
        throwError "the indices and major argument of the brecOn application are not variables:{indentExpr body}"
      unless brecOnExtras.all (·.isFVar) do
        throwError "the extra arguments to the brecOn application are not variables:{indentExpr body}"
      let lvl :: indLevels := us |throwError "Too few universe parameters in .brecOn application:{indentExpr body}"

      let group : Structural.IndGroupInst := { Structural.IndGroupInfo.ofInductiveVal indInfo with
        levels := indLevels, params := brecOnArgs }

      -- We also need to know the number of indices of each type former, including the auxiliary
      -- type formers that do not have IndInfo. We can read it off the motives types of the recursor.
      let numTargetss ← do
        let aux := mkAppN (.const recInfo.name (0 :: group.levels)) group.params
        let motives ← inferArgumentTypesN recInfo.numMotives aux
        motives.mapM fun motive =>
          forallTelescopeReducing motive fun xs _ => pure xs.size

      let recArgInfos ← infos.mapM fun info => do
        let some eqnInfo := Structural.eqnInfoExt.find? (← getEnv) info.name | throwError "{info.name} missing eqnInfo"
        let value ← instantiateLambda info.value xs
        let recArgInfo' ← lambdaTelescope value fun ys _ =>
          Structural.getRecArgInfo info.name numFixed (xs ++ ys) eqnInfo.recArgPos
        let #[recArgInfo] ← Structural.argsInGroup group xs value #[recArgInfo']
          | throwError "Structural.argsInGroup did not return a recArgInfo"
        pure recArgInfo

      let positions : Structural.Positions := .groupAndSort (·.indIdx) recArgInfos (Array.range indInfo.numTypeFormers)

      -- Below we'll need the types of the motive arguments (brecOn argument order)
      let brecMotiveTypes ← inferArgumentTypesN recInfo.numMotives (group.brecOn true lvl 0)
      trace[Meta.FunInd] m!"brecMotiveTypes: {brecMotiveTypes}"
      assert! brecMotiveTypes.size = positions.size

      -- Remove the varying parameters from the environment
      withErasedFVars (ys.map (·.fvarId!)) do
        -- The brecOnArgs, brecOnMotives and brecOnMinor should still be valid in this
        -- context, and are the parts relevant for every function in the mutual group

        -- Calculate the types of the induction motives (natural argument order) for each function
        let motiveTypes ← infos.mapM fun info => do
          lambdaTelescope (← instantiateLambda info.value xs) fun ys _ =>
            mkForallFVars ys (.sort levelZero)
        let motiveArities ← infos.mapM fun info => do
          lambdaTelescope (← instantiateLambda info.value xs) fun ys _ => pure ys.size
        let motiveDecls ← motiveTypes.mapIdxM fun i motiveType => do
          let n := if infos.size = 1 then .mkSimple "motive"
                                     else .mkSimple s!"motive_{i+1}"
          pure (n, fun _ => pure motiveType)
        withLocalDeclsD motiveDecls fun motives => do

          -- Prepare the `isRecCall` that recognizes recursive calls
          let fns := infos.map fun info =>
            mkAppN (.const info.name (info.levelParams.map mkLevelParam)) xs
          let isRecCall : Expr → Option Expr := fun e => do
            if let .some i := motives.indexOf? e.getAppFn then
              if e.getAppNumArgs = motiveArities[i]! then
                return mkAppN fns[i]! e.getAppArgs
            .none

          -- Motives with parameters reordered, to put indices and major first
          let brecMotives ← (Array.zip motives recArgInfos).mapM fun (motive, recArgInfo) => do
            forallTelescope (← inferType motive) fun ys _ => do
              let (indicesMajor, rest) := recArgInfo.pickIndicesMajor ys
              mkLambdaFVars indicesMajor (← mkForallFVars rest (mkAppN motive ys))

          -- We need to pack these motives according to the `positions` assignment.
          let packedMotives ← positions.mapMwith PProdN.packLambdas brecMotiveTypes brecMotives
          trace[Meta.FunInd] m!"packedMotives: {packedMotives}"

          -- Now we can calculate the expected types of the minor arguments
          let minorTypes ← inferArgumentTypesN recInfo.numMotives <|
            mkAppN (group.brecOn true lvl 0) (packedMotives ++ brecOnTargets)
          trace[Meta.FunInd] m!"minorTypes: {minorTypes}"
          -- So that we can transform them
          let (minors', mvars) ← M2.run do
            let mut minors' := #[]
            for brecOnMinor in brecOnMinors, goal in minorTypes, numTargets in numTargetss do
              let minor' ← forallTelescope goal fun xs goal => do
                unless xs.size ≥ numTargets do
                  throwError ".brecOn argument has too few parameters, expected at least {numTargets}: {xs}"
                let targets : Array Expr := xs[:numTargets]
                let genIH := xs[numTargets]!
                let extraParams := xs[numTargets+1:]
                -- open body with the same arg
                let body ← instantiateLambda brecOnMinor targets
                removeLamda body fun oldIH body => do
                  trace[Meta.FunInd] "replacing {Expr.fvar oldIH} with {genIH}"
                  let body ← instantiateLambda body extraParams
                  let body' ← buildInductionBody #[genIH.fvarId!] goal oldIH genIH.fvarId! isRecCall body
                  if body'.containsFVar oldIH then
                    throwError m!"Did not fully eliminate {mkFVar oldIH} from induction principle body:{indentExpr body}"
                  mkLambdaFVars (targets.push genIH) (← mkLambdaFVars extraParams body')
              minors' := minors'.push minor'
            pure minors'
          trace[Meta.FunInd] "processed minors: {minors'}"

          -- Now assemble the mutual_induct theorem
          -- Let-bind the transformed minors to avoid code duplication of possibly very large
          -- terms when we have mutual induction.
          let e' ← withLetDecls `minor minorTypes minors' fun minors' => do
            let mut brecOnApps := #[]
            for info in infos, recArgInfo in recArgInfos, idx in [:infos.size] do
              -- Take care to pick the `ys` from the type, to get the variable names expected
              -- by the user, but use the value arity
              let arity ← lambdaTelescope (← instantiateLambda info.value xs) fun ys _ => pure ys.size
              let e ← forallBoundedTelescope (← instantiateForall info.type xs) arity fun ys _ => do
                let (indicesMajor, rest) := recArgInfo.pickIndicesMajor ys
                -- Find where in the function packing we are (TODO: abstract out)
                let some indIdx := positions.findIdx? (·.contains idx) | panic! "invalid positions"
                let some pos := positions.find? (·.contains idx) | panic! "invalid positions"
                let some packIdx := pos.findIdx? (· == idx) | panic! "invalid positions"
                let e := group.brecOn true lvl indIdx -- unconditionally using binduction here
                let e := mkAppN e packedMotives
                let e := mkAppN e indicesMajor
                let e := mkAppN e minors'
                let e ← PProdN.proj pos.size packIdx e
                let e := mkAppN e rest
                let e ← mkLambdaFVars ys e
                trace[Meta.FunInd] "assembled call for {info.name}: {e}"
                pure e
              brecOnApps := brecOnApps.push e
            mkLetFVars minors' (← PProdN.mk 0 brecOnApps)
          let e' ← abstractIndependentMVars mvars (← motives.back.fvarId!.getDecl).index e'
          let e' ← mkLambdaFVars motives e'

          -- We could pass (usedOnly := true) below, and get nicer induction principles that
          -- do not mention odd unused parameters.
          -- But the downside is that automatic instantiation of the principle (e.g. in a tactic
          -- that derives them from an function application in the goal) is harder, as
          -- one would have to infer or keep track of which parameters to pass.
          -- So for now lets just keep them around.
          let e' ← mkLambdaFVars (binderInfoForMVars := .default) xs e'
          let e' ← instantiateMVars e'
          trace[Meta.FunInd] "complete body of mutual induction principle:{indentExpr e'}"
          pure e'

  unless (← isTypeCorrect e') do
    logError m!"constructed induction principle is not type correct:{indentExpr e'}"
    check e'

  let eTyp ← inferType e'
  let eTyp ← elimOptParam eTyp
  -- logInfo m!"eTyp: {eTyp}"
  let params := (collectLevelParams {} eTyp).params
  -- Prune unused level parameters, preserving the original order
  let us := infos[0]!.levelParams.filter (params.contains ·)

  let inductName :=
    if names.size = 1 then
      names[0]! ++ `induct
    else
      names[0]! ++ `mutual_induct

  addDecl <| Declaration.thmDecl
    { name := inductName, levelParams := us, type := eTyp, value := e' }

  if names.size > 1 then
    projectMutualInduct names inductName

/--
Given a recursively defined function `foo`, derives `foo.induct`. See the module doc for details.
-/
def deriveInduction (name : Name) : MetaM Unit := do
  mapError (f := (m!"Cannot derive functional induction principle (please report this issue)\n{indentD ·}")) do
    if let some eqnInfo := WF.eqnInfoExt.find? (← getEnv) name then
      let unaryInductName ← deriveUnaryInduction eqnInfo.declNameNonRec
      unless eqnInfo.declNameNonRec = name do
        deriveUnpackedInduction eqnInfo unaryInductName
    else if let some eqnInfo := Structural.eqnInfoExt.find? (← getEnv) name then
      deriveInductionStructural eqnInfo.declNames eqnInfo.numFixed
    else
      throwError "{name} is not defined by structural or well-founded recursion"

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
    if let some eqnInfo := Structural.eqnInfoExt.find? env p then
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

 builtin_initialize
   Lean.registerTraceClass `Meta.FunInd
