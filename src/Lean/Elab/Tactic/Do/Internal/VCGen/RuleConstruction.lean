/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf, Vladimir Gladshtein
-/
module

prelude
public import Lean.Elab.Tactic.Do.VCGen.Split
public import Lean.Elab.Tactic.Do.Internal.VCGen.Context
public import Lean.Elab.Tactic.Do.Internal.VCGen.Reduce
public import Lean.Elab.Tactic.Do.Internal.VCGen.SpecDB
public import Lean.Meta.Sym.Apply
public import Lean.Meta.Sym.Util
import Lean.Meta.WHNF

open Lean Meta Elab Tactic Sym
open Lean.Elab.Tactic.Do.Internal.SpecAttr

namespace Lean.Elab.Tactic.Do.Internal

namespace VCGen

/-!
Construction of `BackwardRule`s from `SpecTheorem`s and split info. Pure
`MetaM` — no knowledge of `VCGenM`. The `VCGenM` cache wrappers live in
`VCGen.RuleCache`.
-/

open Std.Internal.Do Lean.Order

/-! ## Logic rules

Backward rules for decomposing lattice logic connectives (`⊓`, `⇨`, `⌜·⌝`, `⊤`) on the RHS of an
entailment `pre ⊑ e s₁ … sₙ`.
-/

/-- A decomposition of a lattice logic connective on the RHS of an entailment. Bundles everything
`LatticeSplit.mkBackwardRuleForLattice` needs: how to rebuild the connective, the pointwise `_apply`
distribution lemma, the `⊑`-form split lemma, and whether the operands depend on the excess (state)
arguments. -/
public structure LatticeSplit where
  /-- Rebuild the connective from its operands `as` and the optional lattice carrier type. -/
  mkLattice : Array Expr → Option Expr → MetaM Expr
  /-- The pointwise `_apply` lemma distributing the connective through function application. -/
  applyLemma : Name
  /-- The `⊑`-form split lemma decomposing `pre ⊑ connective`. -/
  relLemma : Name
  /-- Whether the operands are functions of the excess (state) arguments, and so must be applied to
  each excess argument when descending one lattice level during `mkApplyEq`.

  For `⊓`/`⇨` the operands are themselves elements of the function lattice (`(a ⊓ b) s = a s ⊓ b s`),
  so each operand `a` becomes `a s`. For `⌜·⌝`/`⊤` the operand is reused unchanged
  (`(⌜p⌝ : σ→β) s = (⌜p⌝ : β)`, `(⊤ : σ→β) s = (⊤ : β)`), so it must not be applied to `s`. -/
  needApplyArgs : Bool
  /-- The number of explicit lattice operands the connective takes after its carrier type and
  instance: `2` for `⊓`/`⇨`, `1` for `⌜·⌝`, `0` for `⊤`. -/
  numOperands : Nat

/-- The lattice meet `⊓`. -/
public def LatticeSplit.meet : LatticeSplit where
  mkLattice as _ := mkAppM ``meet as
  applyLemma := ``meet_apply
  relLemma := ``le_meet           -- le_meet (x y z) : x ⊑ y → x ⊑ z → x ⊑ y ⊓ z
  needApplyArgs := true
  numOperands := 2

/-- The Heyting implication `⇨`. -/
public def LatticeSplit.himp : LatticeSplit where
  mkLattice as _ := mkAppM ``himp as
  applyLemma := ``himp_apply
  relLemma := ``himp_complete     -- himp_complete (x a b) : a ⊓ x ⊑ b → x ⊑ a ⇨ b
  needApplyArgs := true
  numOperands := 2

/-- The pure assertion embedding `⌜·⌝`. The `⊤`-fixed split lemma makes the rule apply only when the
precondition is `⊤`, where turning `pre ⊑ ⌜p⌝` into the subgoal `p` is sound. -/
public def LatticeSplit.ofProp : LatticeSplit where
  mkLattice as resultType? :=
    mkAppOptM ``Lean.Order.CompleteLattice.ofProp #[resultType?, none, some as[0]!]
  applyLemma := ``Lean.Order.CompleteLattice.ofProp_apply
  relLemma := ``Lean.Order.top_le_ofProp -- top_le_ofProp (p) : p → ⊤ ⊑ ⌜p⌝
  needApplyArgs := false
  numOperands := 1

/-- The lattice top `⊤`. Has no operands; `le_top` has no premise, so the rule closes the goal. -/
public def LatticeSplit.top : LatticeSplit where
  mkLattice _ resultType? := mkAppOptM ``Lean.Order.top #[resultType?, none]
  applyLemma := ``Lean.Order.top_apply
  relLemma := ``le_top            -- le_top (x) : x ⊑ ⊤  (no premise ⇒ closes the goal)
  needApplyArgs := false
  numOperands := 0

/-- The lattice connectives VCGen decomposes on the RHS of an entailment, keyed by head constant. -/
public def latticeSplits : Std.HashMap Name LatticeSplit :=
  .ofList [
    (``meet, .meet),
    (``himp, .himp),
    (``Lean.Order.CompleteLattice.ofProp, .ofProp),
    (``Lean.Order.top, .top)]

/-- Lift an equality `lhs = rhs` to `(lhs args...) = (rhs args...)`. -/
private def liftEqByArgs (eqPrf : Expr) (args : List Expr) : MetaM Expr := do
  if args.isEmpty then
    return eqPrf
  let eqTy ← inferType eqPrf
  let some (_, lhs, _rhs) := eqTy.eq?
    | throwError "Expected equality proof, got {indentExpr eqTy}"
  let lhsTy ← inferType lhs
  let context ← withLocalDecl `x .default lhsTy fun x => do
    let app := mkAppN x args.toArray
    mkLambdaFVars #[x] app
  mkCongrArg context eqPrf

/--
Apply a pointwise `_apply` lemma repeatedly over all excess arguments, producing an equality at
the fully applied level.

Example (`c = .meet`, `c.applyLemma = ``meet_apply`, `as = #[a, b]`, `ss = [s₁, s₂]`): the resulting
proof has type `((a ⊓ b) s₁ s₂) = (a s₁ s₂ ⊓ b s₁ s₂)`.
-/
private partial def LatticeSplit.mkApplyEq
    (c : LatticeSplit)
    (as : Array Expr) (ss : List Expr) (resultType? : Option Expr := none) : MetaM Expr := do
  match ss with
  | [] => mkEqRefl =<< c.mkLattice as resultType?
  | s :: ss' =>
    let args := as.push s |>.map some
    let rt := resultType?.map .bindingBody!
    let step ← mkAppOptM c.applyLemma <| #[none, rt, none] ++ args
    if ss'.isEmpty then
      return step
    let stepLift ← liftEqByArgs step ss'
    -- Descend one lattice level: only connectives whose operands depend on the excess
    -- arguments (see `LatticeSplit.needApplyArgs`) get their operands applied to `s`.
    let as := if c.needApplyArgs then as.map (mkApp · s) else as
    let rest ← c.mkApplyEq as ss' rt
    mkEqTrans stepLift rest

/-- Distribute a lattice connective through function applications via its `_apply` lemma,
    staying at the lattice level. Returns `((a ⊓ b) s₁…sₙ, eq)` where
    `eq : (a ⊓ b) s₁…sₙ = (a s₁…sₙ ⊓ b s₁…sₙ)`. -/
private def LatticeSplit.mkDistributeEq
    (c : LatticeSplit) (as ss : Array Expr) (resultType? : Option Expr := none) : MetaM (Expr × Expr) := do
  let lat ← c.mkLattice as resultType?
  let goal := mkAppN lat ss
  let eqFun ← c.mkApplyEq as ss.toList resultType?
  return (goal, eqFun)

/--
Creates a reusable backward rule for a lattice connective in `⊑` form.
Chains distribution (`_apply`) with the split lemma (`le_meet`/`himp_complete`).

For `⊓`, produces:
```
∀ (a b : l) (s₁ : σ₁) ... (sₙ : σₙ) (pre : l'),
  pre ⊑ a s₁...sₙ → pre ⊑ b s₁...sₙ → pre ⊑ (a ⊓ b) s₁...sₙ
```
For `⇨`, produces:
```
∀ (a b : l) (s₁ : σ₁) ... (sₙ : σₙ) (pre : l'),
  a s₁...sₙ ⊓ pre ⊑ b s₁...sₙ → pre ⊑ (a ⇨ b) s₁...sₙ
```
Works for any `CompleteLattice`, not just `Prop`.
-/
public def LatticeSplit.mkBackwardRuleForLattice
    (c : LatticeSplit) (as : Array Expr) (excessArgs : Array Expr)
    (resultType? : Option Expr := none)
    : MetaM BackwardRule := do
  let as ← as.mapM fun arg => do
    mkFreshExprMVar (userName := `a) (← Meta.inferType arg)
  let ss ← excessArgs.mapM fun arg => do
    mkFreshExprMVar (userName := `s) (← Meta.inferType arg)

  let (goal, eqGoalDistributed) ← c.mkDistributeEq as ss resultType?

  let goalTy ← Meta.inferType goal
  -- The precondition is a fresh metavariable that becomes a universally quantified parameter of
  -- the rule.
  let pre ← mkFreshExprMVar (userName := `Pre) goalTy

  -- Lift equality through `pre ⊑ ·`: (pre ⊑ goal) = (pre ⊑ distributed)
  -- Use partial application (not lambda) to avoid beta redexes
  let relPreGoal ← mkAppM ``PartialOrder.rel #[pre]
  let relEq ← mkCongrArg relPreGoal eqGoalDistributed
  let relEqSymm ← mkEqSymm relEq
  -- eqMp : (pre ⊑ distributed) → (pre ⊑ goal)
  let eqMp ← mkAppM ``Eq.mp #[relEqSymm]

  -- Instantiate the split lemma (le_meet / himp_complete / top_le_ofProp / le_top) via telescope
  let splitLemma ← mkConstWithFreshMVarLevels c.relLemma
  let (xs, _, body) ← forallMetaTelescope (← Meta.inferType splitLemma)
  -- Unify conclusion with eqMp's domain to assign param mvars
  unless ← isDefEq body (← Meta.inferType eqMp).bindingDomain! do
    throwError "Expected {← Meta.inferType eqMp}.bindingDomain! = {← Meta.inferType body}"
  -- Compose (abstractMVars handles instantiation of assigned mvars)
  let prf := mkApp eqMp (mkAppN splitLemma xs)

  let res ← abstractMVars prf
  mkBackwardRuleFromExpr res.expr res.paramNames.toList

/-! ## Spec rules -/

/-- Build the explicit pointwise implication premise used to weaken a concrete `post`.
    State binders are named positionally from `stateArgNames` (else `s`); their names ride
    on the premise and are later introduced with the right user-facing names. -/
private def mkPostPointwisePremise (postSpec postTarget postTy : Expr) (ssTypes : Array Expr)
    (stateArgNames : Array Name := #[]) : MetaM Expr := do
  let .forallE _ α _ _ := postTy
    | throwError "expected a postcondition function, got {indentExpr postTy}"
  withLocalDeclD `a α fun a => do
    let ssNamesTypes := ssTypes.mapIdx fun i ty => (stateArgNames[i]?.getD `s, ty)
    withLocalDeclsDND ssNamesTypes fun ss' => do
      let lhs := postSpec.betaRev <| ss'.reverse.push a
      let rhs := mkAppN (mkApp postTarget a) ss'
      mkForallFVars (#[a] ++ ss') (← mkAppM ``PartialOrder.rel #[lhs, rhs])

/-- Recursively decompose `epostSpec ⊑ epostAbstract` into per-component proofs.
    - `EPost.Cons.mk head tail` → mvar for `head ⊑ epostAbstract.head`, recurse on tail
    - `EPost.Nil.mk` → trivial via `EPost.Nil.le`
    - Otherwise, if `EPred` is `EPost.Cons`, project `epostSpec.head`/`.tail` and decompose those
    - Otherwise → single mvar for `epostSpec ⊑ epostAbstract` -/
private partial def decomposeEPostRel (EPred epostSpec epostAbstract : Expr)
    (stateArgNames : Array Name := #[]) : MetaM Expr := do
  match_expr epostSpec with
  | EPost.Cons.mk ehTy etTy head tail =>
    let absHead ← mkAppM ``EPost.Cons.head #[epostAbstract]
    let absTail ← mkAppM ``EPost.Cons.tail #[epostAbstract]
    let hTail ← decomposeEPostRel etTy tail absTail stateArgNames
    /- Sometimes, even though `epost` is not schematic itself, its components might be schematic.
      Think of a triple of a kind `⦃ pre ⦄ x ⦃ post; epost₁, ⊥, epost₃, ⊥, ... ⦄`.
      In this case we do not want to create new metavariables for `epost₁`, `epost₃`, etc.
      Instead, we will just assign them to `epostAbstract.tail.head` and
      `epostAbstract.tail.tail.head`, etc. -/
    if head.isMVar then
      head.mvarId!.assign absHead
      mkAppM ``EPost.Cons.mk_le_tail #[tail, epostAbstract, hTail]
    else
      -- Collect state types: e.g. String → Nat → Prop → skip first (exc type), rest are state types
      let ssTypes ← forallTelescope ehTy fun xs _ => xs.drop 1 |>.mapM (Meta.inferType ·)
      let headTy ← Meta.inferType head
      let hHeadTy ← mkPostPointwisePremise head absHead headTy ssTypes stateArgNames
      let hHead ← mkFreshExprMVar (userName := `epostImpl) hHeadTy
      mkAppM ``EPost.Cons.mk_le #[head, tail, epostAbstract, hHead, hTail]
  | EPost.Nil.mk => mkAppM ``EPost.Nil.le #[epostAbstract]
  | _ =>
    match_expr EPred.consumeMData with
    | EPost.Cons ehTy etTy =>
      let specHead ← mkAppM ``EPost.Cons.head #[epostSpec]
      let specTail ← mkAppM ``EPost.Cons.tail #[epostSpec]
      let absHead ← mkAppM ``EPost.Cons.head #[epostAbstract]
      let absTail ← mkAppM ``EPost.Cons.tail #[epostAbstract]
      let headTy ← Meta.inferType specHead
      -- Collect state types: e.g. String → Nat → Prop → skip first (exc type), rest are state types
      let ssTypes ← forallTelescope ehTy fun xs _ => xs.drop 1 |>.mapM (Meta.inferType ·)
      let hHeadTy ← mkPostPointwisePremise specHead absHead headTy ssTypes stateArgNames
      let hHead ← mkFreshExprMVar (userName := `epostImpl) hHeadTy
      let hTail ← decomposeEPostRel etTy specTail absTail stateArgNames
      mkAppM ``EPost.Cons.mk_le #[specHead, specTail, epostAbstract, hHead, hTail]
    | EPost.Nil => mkAppM ``EPost.Nil.le #[epostAbstract]
    | _ =>
      let hTy ← mkAppM ``PartialOrder.rel #[epostSpec, epostAbstract]
      mkFreshExprMVar (userName := `epostImpl) hTy

/--
Create the proof term for the backward rule built from an instantiated spec theorem.
In order for the backward rule to apply, the concrete precondition, postcondition and exception
postcondition appearing in the spec may need to be generalized into rule parameters, emitting
verification conditions for the generalization.

### General idea

Consider the spec theorem `WPMonad.bind_le_wp_bind`:
```
WPMonad.bind_le_wp_bind :
  wp x (fun a => wp (f a) post epost) epost ⊑ wp (x >>= f) post epost
```
This theorem is already in WP-form, so `post` and `epost` are schematic. However, its precondition
`wp x (fun a => wp (f a) post epost) epost` is not. Hence we must emit a VC for the precondition:
```
prf : ∀ {α β} (x : m α) (f : α → m β) (post : β → Pred) (epost : EPred)
  (pre : Pred) (hpre : pre ⊑ wp x (fun a => wp (f a) post epost) epost),
  pre ⊑ wp (x >>= f) post epost
```
The proof term is constructed with `PartialOrder.rel_trans hpre WPMonad.bind_le_wp_bind`.

#### Postcondition VCs

Similarly, a VC is generated for the postcondition if it is not schematic. For example, a
hypothetical restrictive spec for `pure` could be:
```
myPure.spec (n : Nat) : (⊤ : Prop) ⊑ wp (myPure n) (fun r => r = n) epost
```
This yields a backward rule of the form:
```
prf : ∀ (n : Nat) (pre : Prop) (hpre : pre ⊑ True)
  (post : Nat → Prop) (hpost : ∀ r, r = n ⊑ post r) (epost : EPost⟨⟩),
  pre ⊑ wp (myPure n) post epost
```
The postcondition VC is pointwise over the return value and over any excess state arguments. The
proof is generalized with `WP.wp_consequence_le`.

#### Exception postcondition VCs

A VC is also generated for the exception postcondition if it is not schematic. For an `EPost.Cons`
value, the relation `epostSpec ⊑ epost` is decomposed component by component:
```
∀ e s₁ ... sₙ, epostSpec.head e s₁ ... sₙ ⊑ epost.head e s₁ ... sₙ
```
and recursively for the tail. `decomposeEPostRel` assembles these component VCs using
`EPost.Cons.mk_le` and `EPost.Nil.le`; the proof is then generalized with `WP.wp_econs_le`.
When the spec exception postcondition is `⊥`, no VC is needed and `WP.wp_econs_bot_le` is
used instead.

#### Excess state arguments

Furthermore, when there are excess state arguments `[s₁, ..., sₙ]` involved, the proof is
specialized to those arguments:
```
... :
  pre ⊑ wp x (fun a => wp (f a) post epost) epost s₁ ... sₙ →
  pre ⊑ wp (x >>= f) post epost s₁ ... sₙ
```
The precondition and all generated pointwise postcondition premises are applied to these same state
arguments.

### Caching

It turns out we can cache backward rules for the cache key
`(specThm.proof.key, instWP, excessArgs.size)`. This is important for performance and helps avoid
rebuilding the same rule for every goal that uses the same spec theorem, `WPMonad` instance and
number of excess state arguments. We do that in the `VCGenM` wrapper
`mkBackwardRuleFromSpecCached`.

The rule is built from the abstracted proof returned here via `mkBackwardRuleFromExpr`. This keeps
the proof construction reusable even when the proof still contains free variables from the goal
context, such as generic monad or WP instance parameters.

### Specialization

It is unnecessary to use the `bind` rule in full generality. It is much more efficient to specialize
it for the particular predicate type, exception postcondition type and `WPMonad` instance.
`tryMkBackwardRuleFromSpec` does that by instantiating the spec theorem and checking that its
`Pred` and `WPMonad` arguments match the ones from the use site.

For `StateM Nat` and one excess state arg `s`, the type produced for `WPMonad.bind_le_wp_bind` becomes
```
prf : ∀ (pre : Prop) (α : Type) (x : StateT Nat Id α) (β : Type)
  (f : α → StateT Nat Id β) (post : β → Nat → Prop) (epost : EPost⟨⟩) (s : Nat),
  pre ⊑ wp x (fun a => wp (f a) post epost) epost s →
  pre ⊑ wp (x >>= f) post epost s
```
-/
private def mkSpecBackwardProof
    (pre prog postSpec epostSpec specProof EPred : Expr) (ss ssTypes : Array Expr)
    (stateArgNames : Array Name := #[]) : MetaM AbstractMVarsResult := do
  /- we start with `pre ⊑ wp prog post epost` where
  1. `pre` represents the Lean expression for `pre`
  2. `prog`, `postSpec`, and `epostSpec` are the selected arguments of the spec's `wp` RHS
  3. `specProof` is the proof of the spec `pre ⊑ wp prog postSpec epostSpec`
  4. `ss` represents the Lean expressions for the state variables `s1`, `s2`, ..., `sn`
  5. `ssTypes` represents the Lean types for the state variables `s1`, `s2`, ..., `sn` -/
  let mut postAbstract := postSpec.consumeMData
  let mut epostAbstract := epostSpec.consumeMData
  let mut specApplied := specProof

  /- abstract concrete `post` if it is not already abstract -/
  unless postAbstract.isMVar do
    /- `α → Pred`: type of `post` -/
    let postTy ← Meta.inferType postSpec
    /- mvar `postAbstract` for new abstract `post` -/
    postAbstract ← mkFreshExprMVar (userName := `Post) postTy
    /- premise type `∀ (a : α) (s₁ : σ₁) ... (sₙ : σₙ), postSpec a s₁ ... sₙ → postAbstract a s₁ ... sₙ` -/
    let hpostTy ← mkPostPointwisePremise postSpec postAbstract postTy ssTypes stateArgNames
    /- mvar `?postImpl` for the proof of the premise -/
    let hpost ← mkFreshExprMVar (userName := `postImpl) hpostTy
    /- `wp_consequence_le` expects its premise at the *function-lattice* order `postSpec ⊑ postAbstract`,
       whereas `hpost` is stated pointwise (`∀ a s…, postSpec a s… ⊑ postAbstract a s…`). The two are
       defeq, but unfolding the function-lattice `⊑` instance is blocked when the post's domain is a
       metavariable (e.g. the accumulator `β` of a `forIn` loop spec). Cast `hpost` to the function
       order here so the defeq is forced at this depth, keeping the user-facing VC pointwise. -/
    let relTy ← mkAppM ``PartialOrder.rel #[postSpec, postAbstract]
    let hpostRel ← mkExpectedTypeHint hpost relTy
    /- get the proof of `pre ⊑ wp prog postAbstract epostSpec`, where `post` is abstracted.
       Uses wp_consequence_le: post ⊑ post' → pre ⊑ wp x post epost → pre ⊑ wp x post' epost -/
    specApplied ← mkAppM ``WP.wp_consequence_le #[prog, postSpec, postAbstract, epostSpec, hpostRel, specApplied]

  /- abstract concrete `epost` if it is not already abstract -/
  unless epostAbstract.isMVar do
    /- `EPost⟨t₁, t₂, ..., tₙ⟩`: type of `epost` -/
    let epostTy ← Meta.inferType epostSpec
    /- mvar `epostAbstract` for new abstract `epost` -/
    epostAbstract ← mkFreshExprMVar (userName := `EPost) epostTy
    /- if `epost` is `⊥`, then `epost ⊑ epostAbstract` holds trivially and
      abstracting `epost` can be simply done by `WP.wp_econs_bot_le` without
      introducing a new premise. This case is quite common, that's why we handle
      it specially. -/
    let isBot ← try
        let botEPost ← mkAppOptM ``Lean.Order.bot #[epostTy, none]
        isDefEqGuarded epostSpec botEPost
      catch _ => pure false
    if isBot then
      /- get the proof of `pre ⊑ wp prog postAbstract epostAbstract`, where `epost (= ⊥)` is abstracted.
        This proof DOES NOT have a `?epostImpl` premise -/
      specApplied ← mkAppM ``WP.wp_econs_bot_le #[prog, postAbstract, epostAbstract, specApplied]
    else
      /- Decompose `epostSpec ⊑ epostAbstract` into per-component proofs
        using `EPost.Cons.mk_le` and `EPost.Nil.le` -/
      let hepost ← decomposeEPostRel EPred epostSpec epostAbstract stateArgNames
      specApplied ← mkAppM ``WP.wp_econs_le #[prog, postAbstract, epostSpec, epostAbstract, hepost, specApplied]

  /- By default we always abstract `pre`, since in most of the specifications
    `pre` is not schematic. In exceptional cases, where `pre` is schematic, it
    is redundant, but we still do that to keep the code simple.

    Here we also apply the excess state arguments to `pre` and `wp prog postAbstract epostAbstract` -/
  /- use `beta` to create `pre s₁ ... sₙ`  to avoid creating beta redexes when `pre` is a lambda -/
  let preApplied := pre.beta ss
  /- proof of the original theorem with abstracted `post` and `epost` specialized to the excess state arguments -/
  specApplied := mkAppN specApplied ss
  /- `wp prog postAbstract epostAbstract s₁ ... sₙ` -/
  let wpTy ← mkAppM ``Std.Internal.Do.wp <| #[prog, postAbstract, epostAbstract] ++ ss
  let specAppliedTy ← mkAppM ``PartialOrder.rel #[preApplied, wpTy]
  /- later when the whole proof is type checked, we want to help the kernel by providing the expected type -/
  specApplied ← mkExpectedTypeHint specApplied specAppliedTy
  let preAppliedTy ← Meta.inferType preApplied
  /- create a new mvar for the abstracted `pre` -/
  let preAbstract ← mkFreshExprMVar (userName := `Pre) preAppliedTy
  let specAbstractTy ← mkAppM ``PartialOrder.rel #[preAbstract, preApplied]
  /- create a new mvar for the proof of the abstracted `pre` -/
  let specAbstract ← mkFreshExprMVar (userName := `vc) specAbstractTy
  /- use `PartialOrder.rel_trans` to compose the abstracted `pre` and the proof of the original theorem -/
  specApplied ← mkAppM ``PartialOrder.rel_trans #[specAbstract, specApplied]

  abstractMVars specApplied

/--
Normalize an instantiated equality spec `lhs = rhs` (both of type `info.m α`) to the `⊑ wp` form
`wp rhs Q E ⊑ wp lhs Q E` by instantiating `wp_le_wp_of_eq` with fresh schematic `Q`/`E`.

The schematic `Q`/`E` make the postcondition and exception-postcondition VCs collapse in
`mkSpecBackwardProof`, so the resulting rule rewrites a `wp lhs` goal to a `wp rhs` premise, matching
the equational behaviour of a simp spec. Leftover dictionary metavariables (abstract-monad equations
such as `Spec.UnfoldLift.get`) are synthesized first, and dictionary projections in `rhs` are reduced
so the RHS exposes the actual operation (e.g. `MonadState.modifyGet`'s RHS `inst.modifyGet` reduces to
`MonadStateOf.modifyGet`). Reducing, rather than folding the projection, is essential: folding would
turn it back into the keyed head `MonadState.modifyGet` and the rewrite would loop.
-/
private def eqSpecToWp? (info : WPInfo) (xs : Array Expr) (eqPrf eqType : Expr) :
    OptionT MetaM (Expr × Expr) := do
  let_expr Eq eqα lhs rhs := eqType
    | throwError "simp spec is not an equation: {eqType}"
  -- Recover the value type `α` and confirm the equation is in the goal's monad. `α` is typed at the
  -- monad's domain sort so the equation's element type stays well-formed.
  let α ← mkFreshExprMVar (← inferType info.m).bindingDomain!
  guard <| ← isDefEqGuarded eqα (mkApp info.m α)
  -- Pin the schematic instance and state metavariables by unifying the equation's LHS with the goal's
  -- concrete program, so dictionary projections in `rhs` reduce against the real instance.
  let _ ← show MetaM Bool from commitWhen <| isDefEqGuarded lhs info.prog
  -- Synthesize leftover dictionary metavariables (e.g. for an abstract-monad lift equation, whose LHS
  -- does not unify with a concrete program) so the projections in `rhs` reduce against instances.
  for x in xs do
    if x.isMVar && !(← x.mvarId!.isAssigned) then
      try x.mvarId!.assign (← Meta.synthInstance (← Meta.inferType x))
      catch _ => pure ()
  -- Reduce dictionary projections to expose the actual operation VCGen continues on.
  let rhs ← show MetaM Expr from Meta.transform rhs (pre := fun e => do
    if let .proj .. := e then
      if let some r ← withDefault <| Meta.reduceProj? e then return .done r
    return .continue)
  -- `post`/`epost` are schematic metavariables (their VCs collapse downstream).
  let post ← mkFreshExprMVar (userName := `Q) (← mkArrow α info.Pred)
  let epost ← mkFreshExprMVar (userName := `E) info.EPred
  -- Cast to the reduced RHS so the resulting `wp` rewrites onto the exposed operation.
  let eqPrf ← mkExpectedTypeHint eqPrf (← mkEq lhs rhs)
  -- Pin the monad and assertion instances from the goal's `wp` arguments. Inferring the monad from
  -- the equation type alone would leave `m β =?= info.m γ` as an underdetermined flex-rigid problem,
  -- so non-monadic equations like `Option.getD.eq_1` would fail to unify. With `m` fixed, the value
  -- type is inferred from the equation proof.
  let specProof ← mkAppOptM ``Std.Internal.Do.wp_le_wp_of_eq <|
    (info.args.extract 0 7).map some ++ #[none, none, some eqPrf, some post, some epost]
  return (specProof, ← instantiateMVars (← Meta.inferType specProof))

/--
Try to build a backward rule from a single spec theorem.

For a spec already in `⊑ wp` form (`pre ⊑ wp prog post epost`, where the lattice type is
`info.Pred = σ1 → ... → σn → Prop`), produces an auxiliary lemma directly. An equality spec
`lhs = rhs` is first normalized to `wp rhs Q E ⊑ wp lhs Q E` via `eqSpecToWp?` and then handled the
same way.

- `info.Pred`: the goal's lattice type (e.g. `Nat → Prop`)
- `info.instWP`: the `WPMonad` instance for the goal monad
- `info.excessArgs`: free variables representing state args from
  `info.Pred = σ1 → ... → σn → Prop`
-/
public def tryMkBackwardRuleFromSpec (specThm : SpecTheorem) (info : WPInfo)
    (stateArgNames : Array Name := #[]) : OptionT MetaM BackwardRule := do
  -- Instantiate the spec theorem, creating metavars for all universally quantified params
  let (xs, _bs, specProof, specType) ← specThm.instantiate
  -- Equality specs (the simp side of `@[spec]`) are normalized to `⊑ wp` form, then handled like
  -- any ordinary `⊑ wp` spec.
  let (specProof, specType) ←
    if specType.isAppOfArity ``Eq 3 then eqSpecToWp? info xs specProof specType
    else pure (specProof, specType)
  let_expr PartialOrder.rel Pred' _cl' pre rhs := specType
    | throwError "target not a partial order ⊑ application {specType}"
  guard <| ← isDefEqGuarded info.Pred Pred'
  let_expr Std.Internal.Do.wp _Prog' _Value' _Pred' _EPred' _instAL' _instEAL' instWP' prog postSpec epostSpec := rhs
    | throwError "target not a wp application {rhs}"
  guard <| ← isDefEqGuarded info.instWP instWP'
  -- Use local excess-state binders so explicit post premises can be re-lifted to `⊑`.
  -- Name them positionally from `stateArgNames` (else `s`) so the rule's binders carry good names.
  let mut ss := #[]
  let mut ssTypes := #[]
  for h : i in [0:info.excessArgs.size] do
    let ty ← Meta.inferType info.excessArgs[i]
    ssTypes := ssTypes.push ty
    ss := ss.push <| ← mkFreshExprMVar (userName := stateArgNames[i]?.getD `s) ty
  let res ← mkSpecBackwardProof pre prog postSpec epostSpec specProof info.EPred ss ssTypes stateArgNames
  mkBackwardRuleFromExpr res.expr res.paramNames.toList

/-! ## Split rules -/

open Lean.Elab.Tactic.Do in
/-- Creates a reusable backward rule for splitting `ite`, `dite`, or matchers.

Uses `SplitInfo.withAbstract` to introduce abstract fvars for the split components,
then `SplitInfo.splitWith` to build the splitting proof. Hypothesis types are
discovered via `rwIfOrMatcher` inside the splitter telescope. -/
public def mkBackwardRuleForSplit
    (splitInfo : SplitInfo) (info : WPInfo) : MetaM BackwardRule := do
  -- The split value type is the goal's, so reuse the goal's program type and `WP` instance directly.
  let a := info.Value
  let ma := info.progTy
  let prf ←
    splitInfo.withAbstract ma fun abstractInfo splitFVars => do
    -- Eta-reduce matcher alts for the backward rule pattern to avoid expensive
    -- higher-order unification. The alts are eta-expanded by `withAbstract` so that
    -- `splitWith`/`matcherApp.transform` can `instantiateLambda` them directly.
    let abstractProg := match abstractInfo with
      | .ite e | .dite e => e
      | .matcher matcherApp =>
        { matcherApp with alts := matcherApp.alts.map Expr.eta }.toExpr
    let excessArgNamesTypes ← info.excessArgs.mapM fun arg =>
      return (`s, ← Meta.inferType arg)
    withLocalDeclsDND excessArgNamesTypes fun ss => do
    withLocalDeclD `Post (← mkArrow a info.Pred) fun post => do
    withLocalDeclD `EPost info.EPred fun epost => do
    let mkWP (prog : Expr) : Expr :=
      let args := info.args.take 7 ++ #[prog, post, epost]
      mkAppN (mkAppN info.head args) ss
    let Pred' ← Meta.inferType (mkWP abstractProg)
    withLocalDeclD `Pre Pred' fun pre => do
    let sampleGoal ← mkAppM ``PartialOrder.rel #[pre, mkWP abstractProg]
    let relArgs := sampleGoal.getAppArgs
    let relHead := mkAppN sampleGoal.getAppFn (relArgs.extract 0 3)
    let mkGoal (prog : Expr) : Expr := mkApp relHead (mkWP prog)
    -- Use synthetic opaque mvars so that `rwIfOrMatcher`'s `assumption` cannot
    -- accidentally assign our subgoal metavariables.
    let subgoals ← splitInfo.altInfos.mapM fun _ =>
      mkFreshExprSyntheticOpaqueMVar (mkSort 0)
    let namedSubgoals := subgoals.mapIdx fun i mv => ((`h).appendIndexAfter (i+1), mv)
    withLocalDeclsDND namedSubgoals fun subgoalHyps => do
    let prf ←
      abstractInfo.splitWith
        (useSplitter := true)
        (mkGoal abstractProg)
        (fun _name bodyType idx altFVars => do
          -- Extract the program from `bodyType` (the substituted alt goal type).
          -- For matchers, `bodyType` has the discriminant replaced by the constructor
          -- pattern (e.g., `Nat.zero` instead of `discr`), which is required for
          -- `rwMatcher` to discharge the equality hypotheses of congr equation theorems.
          -- For ite/dite, `bodyType` equals `mkGoal abstractProg` so this is equivalent.
          let prog := bodyType.getArg! 3 |>.getArg! 7
          let res ← rwIfOrMatcher idx prog
          if res.proof?.isNone then
            throwError "mkBackwardRuleForSplit: rwIfOrMatcher failed for alt {idx}"
          let altParams := altFVars.all
          subgoals[idx]!.mvarId!.assign (← mkForallFVars altParams (mkGoal res.expr))
          let context ← withLocalDecl `x .default ma fun x =>
            mkLambdaFVars #[x] (mkGoal x)
          let eqProof ← mkAppM ``congrArg #[context, res.proof?.get!]
          mkEqMPR eqProof (mkAppN subgoalHyps[idx]! altParams))
    let prf ← instantiateMVars prf
    mkLambdaFVars (splitFVars ++ ss ++ #[post, epost, pre] ++ subgoalHyps) prf
  let prf ← instantiateMVars prf
  let res ← abstractMVars prf
  mkBackwardRuleFromExpr res.expr res.paramNames.toList

end VCGen
end Lean.Elab.Tactic.Do.Internal
