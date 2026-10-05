/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Elab.Tactic.VCGen.Context
public import Lean.Elab.Tactic.VCGen.WPApp
import Lean.Meta.Sym.InferType
import Lean.Meta.Sym.InstantiateMVarsS
import Lean.Meta.Sym.InstantiateS
import Lean.Meta.Sym.AbstractS
import Lean.Meta.Sym.Intro
import Lean.Elab.Tactic.VCGen.Util

open Lean Meta Sym Sym.Internal
open Lean.Order

namespace Lean.Elab.Tactic.VCGen

/-!
# Join points (`vcgen +jp`)

The do-elaborator shares the code after an `if` or a `match` through a join point. This module
lets `vcgen +jp` prove that code once instead of once per branch. For example,

```
def f (n : Nat) : Id Nat := do
  let mut x := 0
  if n > 0 then x := 1 else x := 2
  return x + 1
```

elaborates to

```
have __do_jp := fun (r : Unit) (x : Nat) => pure (x + 1)
if n > 0 then __do_jp () 1 else __do_jp () 2
```

Without `+jp`, `vcgen` unfolds `__do_jp` at each jump, so `k` consecutive splits give `2ᵏ` copies
of the shared code. With `+jp`, `vcgen` takes three steps:

1. `registerJoinPoint` creates `?H : Unit → Nat → Prop` and binds
   `__do_jp_spec : ∀ r x, ?H r x → ⊤ ⊑ wp⟦__do_jp r x⟧ Q` in the goal of the `if`. It adds the goal
   `∀ r x, ?H r x → ⊤ ⊑ wp⟦pure (x + 1)⟧ Q` for the body of `__do_jp`.
2. In the `then` branch, `jump?` builds the payload
   `P₁ := fun r x => n > 0 ∧ r = () ∧ x = 1`, which closes over the locals of the branch,
   here the condition `n > 0`. It closes the goal `⊤ ⊑ wp⟦__do_jp () 1⟧ Q` with
   `__do_jp_spec () 1 (?link₁ () 1 p₁)`, where `p₁ : P₁ () 1` holds by the condition and `rfl`. The
   metavariable `?link₁ : ∀ r x, P₁ r x → ?H r x` waits for step 3. The `else` branch uses
   `P₂ := fun r x => ¬n > 0 ∧ r = () ∧ x = 2`.
3. `vcgen` reaches the body goal after all goals of the `if`, so both jumps are known by then.
   `finalizeJoinPoint` sets `?H := fun r x => P₁ r x ∨ P₂ r x`, `?link₁ := fun r x h => Or.inl h`,
   and `?link₂ := fun r x h => Or.inr h`.

The body goal of step 1 thus receives the hypothesis

```
(n > 0 ∧ r = () ∧ x = 1) ∨ (¬n > 0 ∧ r = () ∧ x = 2)
```

For a stateful program, `?H` also takes the states, and each payload equates them with the states
at its jump. In `StateM Nat`, the payload of `__do_jp () 1` in state `t` is
`fun r x s => n > 0 ∧ r = () ∧ x = 1 ∧ s = t`.

The proof term binds `__do_jp_spec` with a `let`, so all jumps share one proof of the body.
-/

/-- Whether `vcgen +jp` handles the program-head `let x := val` as a join point. -/
public def isJoinPointLet (x : Name) (val : Expr) : VCGenM Bool :=
  return (← read).useJP && Lean.Elab.Tactic.Do.isJP x && val.isLambda

/-- The lattice instance of `B`, for `Pred = ∀ s₁ … sₙ, B` and the states `ss = #[s₁, …, sₙ]`,
read off the instance `instCL` of `Pred`, which nests one `instCompleteLatticePi` per state. -/
private def baseInstance? (instCL : Expr) (ss : Array Expr) : SymM (Option Expr) := do
  let mut inst := instCL
  for s in ss do
    let_expr instCompleteLatticePi _ _ f := inst | return none
    inst ← betaS f #[s]
  -- The goals of `vcgen` state `⌜·⌝` with `c`, not with `Assertion.toCompleteLattice (.mk c)`.
  let_expr Std.WP.Assertion.toCompleteLattice _ a := inst | return some inst
  let_expr Std.WP.Assertion.mk _ c := a | return some inst
  return some c

/-- Register the join point `jp := val` that `wpLet?` introduced into the goal
`goal : pre ⊑ wp⟦…⟧ post eposts ss` over the states `ss`. Returns `scope` with `jp`, `goal` with
`__do_jp_spec : ∀ xs ss, ?H xs ss → ⊤ ⊑ wp⟦jp xs⟧ post eposts ss`, and the body goal
`∀ xs ss, ?H xs ss → ⊤ ⊑ wp⟦val xs⟧ post eposts ss`. Returns `none` if the states have no base
lattice instance. -/
public def registerJoinPoint (scope : Scope) (goal : MVarId) (jp : FVarId) (val : Expr)
    (info : WPApp) : VCGenM (Option (Scope × List MVarId)) := goal.withContext do
  let goalTy ← goal.getType
  let_expr PartialOrder.rel α inst _ _ := goalTy | return none
  let jpTy ← Sym.inferType (.fvar jp)
  let numParams ← Lean.Elab.Tactic.Do.getNumJoinParams jpTy info.Prog
  -- `Assertion` is a class abbreviation: `instAL` is `Assertion.mk instCL`, where `instCL` is the
  -- lattice instance of every elaborated `⌜·⌝`, or it is a local instance.
  let instCL ← match_expr info.instAL with
    | Std.WP.Assertion.mk _ instCL => pure instCL
    | _ =>
      let lvls := (← Sym.inferType info.instAL).getAppFn.constLevels!
      mkAppNS (mkConst ``Std.WP.Assertion.toCompleteLattice lvls) #[info.Pred, info.instAL]
  let lctx ← getLCtx
  let localInsts ← getLocalInstances
  let some (hyp, top, specTy, bodyTy) ← forallBoundedTelescope jpTy numParams fun xs _ => do
      forallBoundedTelescope info.Pred info.excessArgs.size fun ss B => do
    let some instB ← baseInstance? instCL ss | return none
    let some u := (← Sym.getLevel B).dec | throwError "vcgen +jp: `{B}` is not a type"
    let top ← mkAppNS (mkConst ``Lean.Order.top [u]) #[B, instB]
    let hyp ← mkFreshExprMVarAt lctx localInsts (← mkForallFVarsS (xs ++ ss) (mkSort .zero))
      .syntheticOpaque
    let entails (prog : Expr) : VCGenM Expr := do
      let wp ← mkAppNS (← mkAppNS info.head (info.args.set! 7 prog)) ss
      let rel ← mkAppNS (mkConst ``PartialOrder.rel goalTy.getAppFn.constLevels!) #[α, inst, top, wp]
      mkForallFVarsS (xs ++ ss) (← mkForallS `h .default (← mkAppNS hyp (xs ++ ss)) rel)
    return some (hyp.mvarId!, top, ← entails (← mkAppNS (.fvar jp) xs), ← entails (← betaS val xs))
    | return none
  let body ← mkFreshExprSyntheticOpaqueMVar bodyTy (← goal.getTag)
  let goal ← goal.replaceTargetDefEqFast (← mkLetS `__do_jp_spec specTy body goalTy)
  let .goal decls goal ← Sym.introN goal 1
    | throwError "vcgen +jp: failed to introduce the proof of{indentExpr specTy}"
  let lctxSize := (← goal.getDecl).lctx.numIndices
  let joinPoint : JoinPoint :=
    { spec := .fvar decls[0]!, top, hyp, numStates := info.excessArgs.size, lctxSize }
  modify fun s => { s with joinPointBodies := s.joinPointBodies.insert body.mvarId! joinPoint }
  return some ({ scope with joinPoints := scope.joinPoints.insert jp joinPoint }, [goal, body.mvarId!])

/-- The payload `fun xs => ∃ ys, xs = args` of a jump over the `locals` `ys`, and the witnesses of
its `∃` and its hypotheses. Here `xs` and `args` include the states. A used `let` local stays a
`let`, and a hypothesis that nothing depends on becomes a conjunct. -/
private def mkPayload (jp : JoinPoint) (args : Array Expr) (locals : Array LocalDecl) :
    VCGenM (Expr × Array Expr) := do
  forallTelescope (← jp.hyp.getType) fun xs _ => do
    let eqs ← xs.mapIdxM fun i x => do
      let α ← Sym.inferType x
      return mkApp3 (mkConst ``Eq [← Sym.getLevel α]) α x args[i]!
    -- `mkLambdaFVars`/`mkLetFVars` re-scope a metavariable whose local context contains `decl`,
    -- such as the invariant of a loop in the branch.
    let body ← locals.foldrM (init := mkAndN eqs.toList) fun decl φ => do
      if decl.value?.isSome then
        mkLetFVars #[decl.toExpr] φ (generalizeNondepLet := false)
      else
        let lam ← mkLambdaFVars #[decl.toExpr] φ
        -- A conjunct needs no instantiation in its proof, where each `∃` copies the rest.
        if (← Sym.inferType decl.type).isProp && !lam.bindingBody!.hasLooseBVars then
          return mkAnd decl.type lam.bindingBody!
        return mkApp2 (mkConst ``Exists [← Sym.getLevel decl.type]) decl.type lam
    return (← mkLambdaFVars xs body, (locals.filter (·.value?.isNone)).map (·.toExpr))

/-- A proof of `∃ ys, args = args` from the witnesses `ys`, by `rfl` on each equation. Each
witness proves the `∃` or the conjunct of its local, and the equations follow all of them. -/
private partial def mkPayloadProof (φ : Expr) (witnesses : List Expr) : MetaM Expr := do
  if let .letE _ _ v b _ := φ then
    return ← mkPayloadProof (b.instantiate1 v) witnesses
  match_expr φ with
  | Exists α p =>
    let w :: ws := witnesses | throwError "vcgen +jp: missing witness for{indentExpr φ}"
    return mkApp4 (mkConst ``Exists.intro φ.getAppFn.constLevels!) α p w
      (← mkPayloadProof (p.beta #[w]) ws)
  | And a b =>
    if let w :: ws := witnesses then
      return mkApp4 (mkConst ``And.intro) a b w (← mkPayloadProof b ws)
    return mkApp4 (mkConst ``And.intro) a b
      (← mkPayloadProof a witnesses) (← mkPayloadProof b witnesses)
  | True => return mkConst ``True.intro
  | Eq α lhs _ => return mkApp2 (mkConst ``Eq.refl φ.getAppFn.constLevels!) α lhs
  | _ => throwError "vcgen +jp: unexpected payload{indentExpr φ}"

/-- Close the goal `⊤ ⊑ wp⟦jp args⟧ post eposts ss` of a jump to a join point of `scope` with
`__do_jp_spec args ss (?link args ss p)`. Here `p` proves the jump's payload from its locals, and
`?link : ∀ xs, payload xs → ?H xs` is a fresh metavariable that `finalizeJoinPoint` assigns. A jump
with a precondition other than `⊤` unfolds `jp` instead. -/
public def jump? (scope : Scope) (goal : MVarId) (info : WPApp) :
    VCGenM (Option (List MVarId)) := do
  let some fv := info.prog.getAppFn.fvarId? | return none
  let some jp := scope.joinPoints.get? fv | return none
  goal.withContext do
  let_expr PartialOrder.rel _ _ pre _ := (← goal.getType) | return none
  unless pre == jp.top do return none
  unless info.excessArgs.size == jp.numStates do
    throwError "vcgen +jp: the jump{indentExpr info.prog}\ndoes not have {jp.numStates} states"
  let xs := info.prog.getAppArgs ++ info.excessArgs
  -- An implementation-detail hypothesis would become an `∃` binder, so it stays out of the payload.
  let locals := (← getLCtx).foldl (start := jp.lctxSize) (init := #[]) fun ds d =>
    if d.isImplementationDetail && d.value?.isNone then ds else ds.push d
  let (payload, witnesses) ← mkPayload jp xs locals
  let linkTy ← forallTelescope (← jp.hyp.getType) fun ys _ => do
    mkForallFVars ys (← mkArrow (payload.beta ys) (mkAppN (.mvar jp.hyp) ys))
  let link ← mkFreshExprSyntheticOpaqueMVar linkTy
  let h ← mkAppNS link (xs.push (← mkPayloadProof (← betaS payload xs) witnesses.toList))
  goal.assign (← mkAppNS jp.spec (xs.push h))
  let jump := { payload, link := link.mvarId! }
  modify fun s => { s with jumps := s.jumps.insert jp.hyp ((s.jumps.getD jp.hyp #[]).push jump) }
  return some []

/-- The disjunction of `ps[lo:hi]`, balanced so that each disjunct has depth `O(log (hi - lo))`. -/
private partial def mkOrTree (ps : Array Expr) (lo hi : Nat) : Expr :=
  if hi == lo then mkConst ``False
  else if hi == lo + 1 then ps[lo]!
  else
    let mid := (lo + hi) / 2
    mkOr (mkOrTree ps lo mid) (mkOrTree ps mid hi)

/-- A proof of `φ = mkOrTree ps lo hi` from `h : ps[i]`. -/
private partial def mkOrIntro (φ : Expr) (i lo hi : Nat) (h : Expr) : MetaM Expr := do
  if hi == lo + 1 then
    return h
  let_expr Or a b := φ | throwError "vcgen +jp: expected a disjunction{indentExpr φ}"
  let mid := (lo + hi) / 2
  if i < mid then
    return mkApp3 (mkConst ``Or.inl) a b (← mkOrIntro a i lo mid h)
  else
    return mkApp3 (mkConst ``Or.inr) a b (← mkOrIntro b i mid hi h)

/-- Assign `?H` of `jp` the disjunction of its jumps' payloads, `False` if no jump reaches `jp`,
and each jump's `?link` the injection of its payload. `vcgen` processes the body goal of `jp` after
all goals below the registration, so every jump is known by then. -/
public def finalizeJoinPoint (jp : JoinPoint) : VCGenM Unit := do
  let jumps := (← get).jumps.getD jp.hyp #[]
  modify fun s => { s with jumps := s.jumps.erase jp.hyp }
  forallTelescope (← jp.hyp.getType) fun xs _ => do
    let φ := mkOrTree (jumps.map (·.payload.beta xs)) 0 jumps.size
    jp.hyp.assign (← mkLambdaFVars xs φ)
    for h : i in [:jumps.size] do
      withLocalDeclD `h (jumps[i].payload.beta xs) fun h => do
        jumps[i].link.assign (← mkLambdaFVars (xs.push h) (← mkOrIntro φ i 0 jumps.size h))

end Lean.Elab.Tactic.VCGen
