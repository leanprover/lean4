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
import Lean.Meta.Injective -- for elimOptParam
import Lean.Elab.PreDefinition.WF.Eqns
import Lean.Elab.PreDefinition.WF.PackMutual
import Lean.Elab.Command

/-!
This module contains code to derive, from the definition of a recursive function
(or mutually recursive functions) defined by well-founded recursion, a
**functional induction principle** tailored to proofs about that function(s). For
example from:

```
def ackermann : Nat → Nat → Nat
  | 0, m => m + 1
  | n+1, 0 => ackermann n 1
  | n+1, m+1 => ackermann n (ackermann (n + 1) m)
derive_functional_induction ackermann
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
`if`-`then`-`else` and `match` expressions.

For every recursive call in that branch, an induction hypothesis asserting the
motive for the arguments of the recursive call is provided.
If the recursive call is under binder and it, or its proof of termination,
depend on the the bound values, then these become assumptions on the inductive
hypothesis.

Additionally, the local context of the branch (e.g. the condition of an
if-then-else) is provided as assumptions in the corresponding induction case.

Mutual recursion is supported and results in multiple motives.


## Implementation overview

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
   mirrors the branching structure of `foo`, i.e. replicates `dite` and matcher applications,
   while adjusting their motive. It also unfolds calls to `oldIH` and collects induction hypotheses
   in conditions (see below).

   In particular, when translating a `match` it is prepared to recognize the idiom
   as introduced by `mkFix` via `Lean.Meta.MatcherApp.addArg?`, which refines the type of `oldIH`
   throughout the match. The transformation will replace `oldIH` with `newIH` here.
   ```
        T[(match (motive := fun oldIH => …) y with | … => fun oldIH' => body) oldIH]
    ==> (match (motive := fun newIH => …) y with | … => fun newIH' => T[body]) newIH
   ```

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

-/

set_option autoImplicit false

namespace Lean.Tactic.FunInd

open Lean Elab Meta

/-- Opens the body of a lambda, _without_ putting the free variable into the local context.
This is used when replacing parameters with different expressions.
This way it will not be picked up by metavariables.
-/
def removeLamda {α} (e : Expr) (k : FVarId → Expr →  MetaM α) : MetaM α := do
  let .lam _n _d b _bi := ← whnfD e | throwError "removeLamda: expected lambda, got {e}"
  let x ← mkFreshFVarId
  let b := b.instantiate1 (.fvar x)
  k x b

/-- Replace calls to oldIH back to calls to the original function. At the end, if `oldIH` occurs, an error is thrown. -/
partial def foldCalls (fn : Expr) (oldIH : FVarId) (e : Expr) : MetaM Expr := do
  unless e.containsFVar oldIH do
    return e

  if e.getAppNumArgs = 2 && e.getAppFn.isFVarOf oldIH then
    let #[arg, _proof] := e.getAppArgs | unreachable!
    let arg' ← foldCalls fn oldIH arg
    return .app fn arg'

  if let some matcherApp ← matchMatcherApp? e (alsoCasesOn := true) then
    if matcherApp.remaining.size == 1 && matcherApp.remaining[0]!.isFVarOf oldIH then
      let matcherApp' ← matcherApp.transform
        (onParams := foldCalls fn oldIH)
        (onMotive := fun _motiveArgs motiveBody => do
          let some (_extra, body) := motiveBody.arrow? | throwError "motive not an arrow"
          foldCalls fn oldIH body)
        (onAlt := fun _altType alt => do
          removeLamda alt fun oldIH alt => do
            foldCalls fn oldIH alt)
        (onRemaining := fun _ => pure #[])
      return matcherApp'.toExpr

  if e.getAppArgs.any (·.isFVarOf oldIH) then
    -- Sometimes Fix.lean abstracts over oldIH in a proof definition.
    -- So beta-reduce that definition.

    -- Need to look through theorems here!
    let e' ← withTransparency .all do whnf e
    if e == e' then
      throwError "foldCalls: cannot reduce application of {e.getAppFn} in {indentExpr e} "
    return ← foldCalls fn oldIH e'

  if let some (n, t, v, b) := e.letFun? then
    let t' ← foldCalls fn oldIH t
    let v' ← foldCalls fn oldIH v
    return ← withLocalDecl n .default t' fun x => do
      let b' ← foldCalls fn oldIH (b.instantiate1 x)
      mkLetFun x v' b'

  match e with
  | .app e1 e2 =>
    return .app (← foldCalls fn oldIH e1) (← foldCalls fn oldIH e2)

  | .lam n t body bi =>
    let t' ← foldCalls fn oldIH t
    return ← withLocalDecl n bi t' fun x => do
      let body' ← foldCalls fn oldIH (body.instantiate1 x)
      mkLambdaFVars #[x] body'

  | .forallE n t body bi =>
    let t' ← foldCalls fn oldIH t
    return ← withLocalDecl n bi t' fun x => do
      let body' ← foldCalls fn oldIH (body.instantiate1 x)
      mkForallFVars #[x] body'

  | .letE n t v b _ =>
    let t' ← foldCalls fn oldIH t
    let v' ← foldCalls fn oldIH v
    return ← withLetDecl n t' v' fun x => do
      let b' ← foldCalls fn oldIH (b.instantiate1 x)
      mkLetFVars  #[x] b'

  | .mdata m b =>
    return .mdata m (← foldCalls fn oldIH b)

  | .proj t i e =>
    return .proj t i (← foldCalls fn oldIH e)

  | .sort .. | .lit .. | .const .. | .mvar .. | .bvar .. =>
    unreachable! -- cannot contain free variables, so early exit above kicks in

  | .fvar .. =>
    throwError m!"collectIHs: cannot eliminate unsaturated call to induction hypothesis"


/--
Given proofs of `P₁`, …, `Pₙ`, returns a proof of `P₁ ∧ … ∧ Pₙ`.
If `n = 0` returns a proof of `True`.
If `n = 1` returns the proof of `P₁`.
-/
def mkAndIntroN : Array Expr → MetaM Expr
| #[] => return mkConst ``True.intro []
| #[e] => return e
| es => es.foldrM (start := es.size - 1) (fun a b => mkAppM ``And.intro #[a,b]) es.back

/-- Given a proof of `P₁ ∧ … ∧ Pᵢ ∧ … ∧ Pₙ`, return the proof of `Pᵢ` -/
def mkProjAndN (n i : Nat) (e : Expr) : Expr := Id.run do
  let mut value := e
  for _ in [:i] do
      value := mkProj ``And 1 value
  if i + 1 < n then
      value := mkProj ``And 0 value
  return value


-- Non-tail-positions: Collect induction hypotheses
-- (TODO: Worth folding with `foldCalls`, like before?)
-- (TODO: Accumulated with a left fold)
partial def collectIHs (fn : Expr) (oldIH newIH : FVarId) (e : Expr) : MetaM (Array Expr) := do
  unless e.containsFVar oldIH do
    return #[]

  if e.getAppNumArgs = 2 && e.getAppFn.isFVarOf oldIH then
    let #[arg, proof] := e.getAppArgs  | unreachable!

    let arg' ← foldCalls fn oldIH arg
    let proof' ← foldCalls fn oldIH proof
    let ihs ← collectIHs fn oldIH newIH arg

    return ihs.push (mkAppN (.fvar newIH) #[arg', proof'])

  if let some (n, t, v, b) := e.letFun? then
    let ihs1 ← collectIHs fn oldIH newIH v
    let v' ← foldCalls fn oldIH v
    return ← withLetDecl n t v' fun x => do
      let ihs2 ← collectIHs fn oldIH newIH (b.instantiate1 x)
      let ihs2 ← ihs2.mapM (mkLetFVars (usedLetOnly := true) #[x] ·)
      return ihs1 ++ ihs2

  if let some matcherApp ← matchMatcherApp? e (alsoCasesOn := true) then
    if matcherApp.remaining.size == 1 && matcherApp.remaining[0]!.isFVarOf oldIH then

      let matcherApp' ← matcherApp.transform
        (onParams := foldCalls fn oldIH)
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
              let altIHs ← collectIHs fn oldIH' newIH'.fvarId! alt
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
    return ← collectIHs fn oldIH newIH e'

  if e.getAppArgs.any (·.isFVarOf oldIH) then
    throwError "collectIHs: could not collect recursive calls from call {indentExpr e}"

  match e with
  | .letE n t v b _ =>
    let ihs1 ← collectIHs fn oldIH newIH v
    let v' ← foldCalls fn oldIH v
    return ← withLetDecl n t v' fun x => do
      let ihs2 ← collectIHs fn oldIH newIH (b.instantiate1 x)
      let ihs2 ← ihs2.mapM (mkLetFVars (usedLetOnly := true) #[x] ·)
      return ihs1 ++ ihs2

  | .app e1 e2 =>
    return (← collectIHs fn oldIH newIH e1) ++ (← collectIHs fn oldIH newIH e2)

  | .proj _ _ e =>
    return ← collectIHs fn oldIH newIH e

  | .forallE n t body bi =>
    let t' ← foldCalls fn oldIH t
    return ← withLocalDecl n bi t' fun x => do
      let ihs ← collectIHs fn oldIH newIH (body.instantiate1 x)
      ihs.mapM (mkLambdaFVars (usedOnly := true) #[x])

  | .lam n t body bi =>
    let t' ← foldCalls fn oldIH t
    return ← withLocalDecl n bi t' fun x => do
      let ihs ← collectIHs fn oldIH newIH (body.instantiate1 x)
      ihs.mapM (mkLambdaFVars (usedOnly := true) #[x])

  | .mdata _m b =>
    return ← collectIHs fn oldIH newIH b

  | .sort .. | .lit .. | .const .. | .mvar .. | .bvar .. =>
    unreachable! -- cannot contain free variables, so early exit above kicks in

  | .fvar _ =>
    throwError "collectIHs: could not collect recursive calls, unsaturated application of old induction hypothesis"

def withLetDecls {α} (vals : Array Expr) (k : Array FVarId → MetaM α) (i : Nat := 0) : MetaM α := do
  if h : i < vals.size then
    let e := vals[i]
    withLetDecl s!"IH{i+1}" e (← inferType e) fun a =>
      withLetDecls vals (fun args => k (args.push a.fvarId!)) (i + 1)
  else
    k #[]
termination_by vals.size - i

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
    mvarid ← mvarid.assert s!"IH{i+1}" (← inferType v) v
  return mvarid

/-- Base case of `buildInductionBody`: Construct a case for the final induction hypthesis.  -/
def buildInductionCase (motiveFVar : FVarId) (fn : Expr) (oldIH newIH : FVarId) (toClear toPreserve : Array FVarId)
    (goal : Expr) (IHs : Array Expr) (e : Expr) : MetaM Expr := do
  let IHs := IHs ++ (← collectIHs fn oldIH newIH e)
  let IHs ← deduplicateIHs IHs

  let mvar ← mkFreshExprSyntheticOpaqueMVar goal (tag := `hyp)
  let mut mvarId := mvar.mvarId!
  mvarId ← assertIHs IHs mvarId
  for fvarId in toClear do
    mvarId ← mvarId.clear fvarId
  mvarId ← mvarId.cleanup (toPreserve := toPreserve)
  let (_, _mvarId) ← mvarId.revertAfter motiveFVar
  let mvar ← instantiateMVars mvar
  pure mvar

partial def buildInductionBody (motiveFVar : FVarId) (fn : Expr) (toClear toPreserve : Array FVarId)
    (goal : Expr) (oldIH newIH : FVarId) (IHs : Array Expr) (e : Expr) : MetaM Expr := do

  if e.isDIte then
    let #[_α, c, h, t, f] := e.getAppArgs | unreachable!
    let IHs := IHs ++ (← collectIHs fn oldIH newIH c)
    let c' ← foldCalls fn oldIH c
    let h' ← foldCalls fn oldIH h
    let t' ← withLocalDecl `h .default c' fun h => do
      let t ← instantiateLambda t #[h]
      let t' ← buildInductionBody motiveFVar fn toClear (toPreserve.push h.fvarId!) goal oldIH newIH IHs t
      mkLambdaFVars #[h] t'
    let f' ← withLocalDecl `h .default (mkNot c') fun h => do
      let f ← instantiateLambda f #[h]
      let f' ← buildInductionBody motiveFVar fn toClear (toPreserve.push h.fvarId!) goal oldIH newIH IHs f
      mkLambdaFVars #[h] f'
    let u ← getLevel goal
    return mkApp5 (mkConst ``dite [u]) goal c' h' t' f'

  if let some matcherApp ← matchMatcherApp? e (alsoCasesOn := true) then
    -- Collect IHs from the parameters and discrs of the matcher
    let paramsAndDiscrs := matcherApp.params ++ matcherApp.discrs
    let IHs := IHs ++ (← paramsAndDiscrs.concatMapM (collectIHs fn oldIH newIH))

    -- A match that refines the parameter has been modified by `Fix.lean` to refine the IH,
    -- so we need to replace that IH
    if matcherApp.remaining.size == 1 && matcherApp.remaining[0]!.isFVarOf oldIH then
      let matcherApp' ← matcherApp.transform (useSplitter := true)
        (onParams := foldCalls fn oldIH)
        (onMotive := fun xs _body => do
          -- Remove the old IH that was added in mkFix
          let eType ← newIH.getType
          let motiveBody ← mkArrow eType goal
          -- TODO: Extract the following idiom
          matcherApp.discrs.size.foldRevM (init := motiveBody) fun i motiveBodyAbst => do
            let motiveArg := xs[i]!
            let discr     := matcherApp.discrs[i]!
            let motiveBodyAbst ← kabstract motiveBodyAbst discr
            return motiveBodyAbst.instantiate1 motiveArg)
        (onAlt := fun expAltType alt => do
          removeLamda alt fun oldIH' alt => do
            forallBoundedTelescope expAltType (some 1) fun newIH' goal' => do
              let #[newIH'] := newIH' | unreachable!
              let alt' ← buildInductionBody motiveFVar fn (toClear.push newIH'.fvarId!) toPreserve goal' oldIH' newIH'.fvarId! IHs alt
              mkLambdaFVars #[newIH'] alt')
        (onRemaining := fun _ => pure #[.fvar newIH])
      return matcherApp'.toExpr

    -- A match that does not refine the parameter, but that we still want to split into separate
    -- cases
    if matcherApp.remaining.isEmpty then
      let matcherApp' ← matcherApp.transform (useSplitter := true)
        (onParams := foldCalls fn oldIH)
        (onMotive := fun _xs _body => pure goal)
        (onAlt := fun expAltType alt => do
          buildInductionBody motiveFVar fn toClear toPreserve expAltType oldIH newIH IHs alt)
      return matcherApp'.toExpr

  if let .letE n t v b _ := e then
    let IHs := IHs ++ (← collectIHs fn oldIH newIH v)
    let t' ← foldCalls fn oldIH t
    let v' ← foldCalls fn oldIH v
    return ← withLetDecl n t' v' fun x => do
      let b' ← buildInductionBody motiveFVar fn toClear toPreserve goal oldIH newIH IHs (b.instantiate1 x)
      mkLetFVars #[x] b'

  if let some (n, t, v, b) := e.letFun? then
    let IHs := IHs ++ (← collectIHs fn oldIH newIH v)
    let t' ← foldCalls fn oldIH t
    let v' ← foldCalls fn oldIH v
    return ← withLocalDecl n .default t' fun x => do
      let b' ← buildInductionBody motiveFVar fn toClear toPreserve goal oldIH newIH IHs (b.instantiate1 x)
      mkLetFun x v' b'

  buildInductionCase motiveFVar fn oldIH newIH toClear toPreserve goal IHs e

partial def findFixF {α} (e : Expr) (k : Array Expr → Expr → MetaM α) : MetaM α := do
  lambdaTelescope e fun params body => do
    if body.isAppOf ``WellFounded.fixF then
      k params body
    else
      let body' ← whnf body
      if body == body' then
        throwError "Term {body} is not a fixF application"
      else
        findFixF body' fun args e' => k (params ++ args) e'

/--
Given a definition `foo` defined via `WellFounded.fixF`, derive a suitable induction principle
`foo.induct` for it. See module doc for details.
 -/
def deriveUnaryInduction (name : Name) : MetaM Name := do
  let inductName := .append name `induct
  if ← hasConst inductName then return inductName

  let info ← getConstInfo name
  let e := Expr.const name (info.levelParams.map mkLevelParam)
  findFixF e fun params body => body.withApp fun f fixArgs => do
    -- logInfo f!"{fixArgs}"
    unless params.size > 0 do
      throwError "Term {e} is not a lambda application"
    unless f.isConstOf ``WellFounded.fixF do
      throwError "Term isn’t application of {``WellFounded.fixF}, but of {f}"
    let #[argType, rel, _motive, body, arg, acc] := fixArgs |
      throwError "Application of WellFounded.fixF has wrong arity {fixArgs.size}"
    unless ← isDefEq arg params.back do
      throwError "fixF application argument {arg} is not function argument "
    let [argLevel, _motiveLevel] := f.constLevels! | unreachable!
    -- logInfo body
    -- mkFresh

    let motiveType ← mkArrow argType (.sort levelZero)
    withLocalDecl `motive .default motiveType fun motive => do

    let e' := mkAppN (.const ``WellFounded.fixF [argLevel, levelZero]) #[argType, rel, motive]
    let fn := mkAppN e params.pop
    let body' ← forallTelescope (← inferType e').bindingDomain! fun xs _ => do
      let #[param, genIH] := xs | unreachable!
      -- open body with the same arg
      let body ← instantiateLambda body #[param]
      removeLamda body fun oldIH body => do
        let body' ← buildInductionBody motive.fvarId! fn #[genIH.fvarId!] #[] (.app motive param) oldIH genIH.fvarId! #[] body
        if body'.containsFVar oldIH then
          throwError m!"Did not fully eliminate {mkFVar oldIH} from induction principle body:{indentExpr body}"
        mkLambdaFVars #[param, genIH] body'

    let e' := mkAppN e' #[body', arg, acc]

    let e' ← mkLambdaFVars #[params.back] e'
    let mvars ← getMVarsNoDelayed e'
    for mvar in mvars, i in [:mvars.size] do
      mvar.setUserName s!"case{i+1}"
    let e' ← mkLambdaFVars (binderInfoForMVars := .default) (mvars.map .mvar) e'

    -- We could pass (usedOnly := true) below, and get nicer induction principles that
    -- do do not mention odd unused parameters.
    -- But the downside is that automatic instantiation of the principle (e.g. in a tactic
    -- that derives them from an function application in the goal) is harder, as
    -- one would have to infer or keep track of which parameters to pass.
    -- So for now lets just keep them around.
    let e' ← mkLambdaFVars (binderInfoForMVars := .default) (params.pop ++ #[motive]) e'
    let e' ← instantiateMVars e'

    let eTyp ← inferType e'
    let eTyp ← elimOptParam eTyp
    -- logInfo m!"eTyp: {eTyp}"
    -- logInfo m!"e has MVar: {e'.hasMVar}"
    unless (← isTypeCorrect e') do
      logError m!"failed to derive induction priciple:{indentExpr e'}"
      check e'

    addDecl <| Declaration.thmDecl
      { name := inductName, levelParams := info.levelParams, type := eTyp, value := e' }
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
  -- TODO: Make arities (or varnames) part of eqnInfo
  let arities ← eqnInfo.declNames.mapM fun name => do
      let ci ← getConstInfoDefn name
      lambdaTelescope ci.value fun xs _body => return xs.size - eqnInfo.fixedPrefixSize

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
          let (i, unpackedArgs) ← WF.unpackArg arities packedArg
          let e' := .const eqnInfo.declNames[i]! e.getAppFn.constLevels!
          let e' := mkAppN e' args.pop
          let e' := mkAppN e' unpackedArgs
          let e' := mkAppN e' args[eqnInfo.fixedPrefixSize+1:]
          return .continue e'

    return .continue e)
  mkExpectedTypeHint value t

/-- Given type `A ⊕' B ⊕' … ⊕' D`, return `[A, B, …, D]` -/
partial def unpackPSum (type : Expr) : List Expr :=
  if type.isAppOfArity ``PSum 2 then
    if let #[a, b] := type.getAppArgs then
      a :: unpackPSum b
    else unreachable!
  else
    [type]

/-- Given `A ⊗' B ⊗' … ⊗' D` and `R`, return `A → B → … → D → R` -/
partial def uncurryPSumArrow (domain : Expr) (codomain : Expr) : MetaM Expr := do
  if domain.isAppOfArity ``PSigma 2 then
    let #[a, b] := domain.getAppArgs | unreachable!
    withLocalDecl `x .default a fun x => do
      mkForallFVars #[x] (← uncurryPSumArrow (b.beta #[x]) codomain)
  else
    mkArrow domain codomain

/--
Given expression `e` with type `(x : A ⊗' B ⊗' … ⊗' D) → R[x]`
return expression of type `(x : A) → (y : B) → … → (z : D) → R[(x,y,z)]`
-/
partial def uncurryPSigma (e : Expr) : MetaM Expr := do
  let packedDomain := (← inferType e).bindingDomain!
  go packedDomain packedDomain #[]
where
  go (packedDomain domain : Expr) args : MetaM Expr :=  do
    if domain.isAppOfArity ``PSigma 2 then
      let #[a, b] := domain.getAppArgs | unreachable!
      withLocalDecl `x .default a fun x => do
        mkLambdaFVars #[x] (← go packedDomain (b.beta #[x]) (args.push x))
    else
      withLocalDecl `x .default domain fun x => do
        let args := args.push x
        let packedArg ← WF.mkUnaryArg packedDomain args
        mkLambdaFVars #[x] (e.beta #[packedArg])

/--
Iterated `PSigma.casesOn`: Given `y : a ⊗' b ⊗' …` and a type `codomain`,
and `alt : (x : a) → (y : b) → codomain`, uses `PSigma.casesOn` to invoke `alt` on `y`.

This very is similar to `Lean.Predefinition.WF.mkPSigmaCasesOn`, but takes a lambda rather than
free variables.
-/
partial def mkPSigmaNCasesOn (y : FVarId) (codomain : Expr) (alt : Expr) : MetaM Expr := do
  let mvar ← mkFreshExprSyntheticOpaqueMVar codomain
  let rec go (mvarId : MVarId) (y : FVarId) (ys : Array Expr) : MetaM Unit := mvarId.withContext do
    if (← inferType (mkFVar y)).isAppOfArity ``PSigma 2 then
      let #[s] ← mvarId.cases y | unreachable!
      go s.mvarId s.fields[1]!.fvarId! (ys.push s.fields[0]!)
    else
      let ys := ys.push (mkFVar y)
      mvarId.assign (alt.beta ys)
  go mvar.mvarId! y #[]
  instantiateMVars mvar

/--
Given expression `e` with type `(x : A) → (y : B[x]) → … → (z : D[x,y]) → R`
returns an expression of type `(x : A ⊗' B ⊗' … ⊗' D) → R`.
-/
partial def curryPSigma (e : Expr) : MetaM Expr := do
  let (d, codomain) ← forallTelescope (← inferType e) fun xs codomain => do
    if xs.any (codomain.containsFVar ·.fvarId!) then
      throwError "curryPSum: codomain depends on domain variables"
    let mut d ← inferType xs.back
    for x in xs.pop.reverse do
      d ← mkLambdaFVars #[x] d
      d ← mkAppOptM ``PSigma #[some (← inferType x), some d]
    return (d, codomain)
  withLocalDecl `x .default d fun x => do
    let value ← mkPSigmaNCasesOn x.fvarId! codomain e
    mkLambdaFVars #[x] value

/--
Given type `(a ⊗' b ⊕' c ⊗' d) → e`, brings `a → b → e` and `c → d → e`
into scope as fresh local declarations and passes their FVars to the continuation `k`.
The `name` is used to form the variable names; uses `name1`, `name2`, … if there are multiple.
-/
def withCurriedDecl {α} (name : String) (type : Expr) (k : Array Expr → MetaM α) : MetaM α := do
  let some (d,c) := type.arrow? | throwError "withCurriedDecl: Expected arrow"
  let motiveTypes ← (unpackPSum d).mapM (uncurryPSumArrow · c)
  if let [t] := motiveTypes then
    -- If a singleton, do not number the names.
    withLocalDecl name .default t fun x => do k #[x]
  else
    go motiveTypes #[]
where
  go : List Expr → Array Expr → MetaM α
  | [], acc => k acc
  | t::ts, acc => do
    let name := s!"{name}{acc.size+1}"
    withLocalDecl name .default t fun x => do
      go ts (acc.push x)


/--
Given expression `e` of type `(x : a ⊗' b ⊕' c ⊗' d) → e[x]`, wraps that expression
to produce an expression of the isomorphic type
```
((x: a) → (y : b) → e[.inl (x,y)]) ∧ ((x : c) → (y : d) → e[.inr (x,y)])
```
-/
def deMorganPSumPSigma (e : Expr) : MetaM Expr := do
  let packedDomain := (← inferType e).bindingDomain!
  let unaryTypes := unpackPSum packedDomain
  shareIf (unaryTypes.length > 1) e fun e => do
    let mut es := #[]
    for unaryType in unaryTypes, i in [:unaryTypes.length] do
      -- unary : (x : a ⊗ b) → e[inl x]
      let unary ← withLocalDecl `x .default unaryType fun x => do
          let packedArg ← WF.mkMutualArg unaryTypes.length packedDomain i x
          mkLambdaFVars #[x] (e.beta #[packedArg])
      -- nary : (x : a) → (y : b) → e[inl (x,y)]
      let nary ← uncurryPSigma unary
      es := es.push nary
    mkAndIntroN es
  where
    shareIf (b : Bool) (e : Expr) (k : Expr → MetaM Expr) : MetaM Expr := do
      if b then
        withLetDecl `packed (← inferType e) e fun e => do mkLetFVars #[e] (← k e)
      else
        k e


-- Adapted from PackMutual: TODO: Compare and unify
/--
  Combine/pack the values of the different definitions in a single value
  `x` is `PSum`, and we use `PSum.casesOn` to select the appropriate `preDefs.value`.
  See: `packMutual`.

  Remark: this method does not replace the nested recursive `preDefValues` applications.
  This step is performed by `transform` with the following `post` method.
 -/
private def packValues (x : Expr) (codomain : Expr) (preDefValues : Array Expr) : MetaM Expr := do
  let varNames := preDefValues.map fun val =>
    if val.isLambda then val.bindingName! else `x
  let mvar ← mkFreshExprSyntheticOpaqueMVar codomain
  let rec go (mvarId : MVarId) (x : FVarId) (i : Nat) : MetaM Unit := do
    if i < preDefValues.size - 1 then
      /-
        Names for the `cases` tactics. The names are important to preserve the user provided names (unary functions).
      -/
      let givenNames : Array AltVarNames :=
         if i == preDefValues.size - 2 then
           #[{ varNames := [varNames[i]!] }, { varNames := [varNames[i+1]!] }]
         else
           #[{ varNames := [varNames[i]!] }]
       let #[s₁, s₂] ← mvarId.cases x (givenNames := givenNames) | unreachable!
      s₁.mvarId.assign (mkApp preDefValues[i]! s₁.fields[0]!).headBeta
      go s₂.mvarId s₂.fields[0]!.fvarId! (i+1)
    else
      mvarId.assign (mkApp preDefValues[i]! (mkFVar x)).headBeta
    termination_by preDefValues.size - 1 - i
  go mvar.mvarId! x.fvarId! 0
  instantiateMVars mvar


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
    -- Next parameter is the motive (motive : a ⊗' b ⊕' c ⊗' d → Prop).
    let packedMotiveType := type.bindingDomain!
    -- Bring unpacked motives (motive1 : a → b → Prop and motive2 : c → d → Prop) into scope
    withCurriedDecl "motive" packedMotiveType fun motives => do
      -- Combine them into a packed motive (motive : a ⊗' b ⊕' c ⊗' d → Prop), and use that
      let motive ← forallBoundedTelescope packedMotiveType (some 1) fun xs motiveCodomain => do
        let #[x] := xs | throwError "packedMotiveType is not a forall: {packedMotiveType}"
        let packedMotives ← motives.mapM curryPSigma
        let motiveBody ← packValues x motiveCodomain packedMotives
        mkLambdaFVars xs motiveBody
      let type ← instantiateForall type #[motive]
      let value := mkApp value motive
      -- Bring the rest into scope
      forallTelescope type fun xs _concl => do
        let alts := xs.pop
        let value := mkAppN value alts
        let value ← deMorganPSumPSigma value
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

@[builtin_command_elab Parser.Command.deriveInduction]
def elabDeriveInduction : Command.CommandElab := fun stx => Command.runTermElabM fun _xs => do
  let ident := stx[1]
  let name ← resolveGlobalConstNoOverloadWithInfo ident
  deriveInduction name

end Lean.Tactic.FunInd
