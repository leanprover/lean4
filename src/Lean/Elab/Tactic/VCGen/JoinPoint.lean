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
   `__do_jp_spec : ∀ r x, ⦃⌜?H r x⌝⦄ __do_jp r x ⦃Q⦄` in the goal of the `if`. It adds the goal
   `∀ r x, ⦃⌜?H r x⌝⦄ pure (x + 1) ⦃Q⦄` for the body of `__do_jp`.
2. In the `then` branch, `jump?` builds the payload
   `P₁ := fun r x => ∃ (h : n > 0), r = () ∧ x = 1`, which closes over the locals of the branch,
   here the condition `h`. It closes the goal of `__do_jp () 1` through
   `pre ⊑ ⌜P₁ () 1⌝ ⊑ ⌜?H () 1⌝ ⊑ wp⟦__do_jp () 1⟧ Q`. The first step holds by `h` and `rfl`, and
   the last is `__do_jp_spec () 1`. The middle step is a metavariable
   `?link₁ : ∀ r x, P₁ r x → ?H r x`. The `else` branch uses
   `P₂ := fun r x => ∃ (h : ¬n > 0), r = () ∧ x = 2`.
3. `vcgen` reaches the body goal after all goals of the `if`, so both jumps are known by then.
   `finalizeJoinPoint` sets `?H := fun r x => P₁ r x ∨ P₂ r x`, `?link₁ := fun r x h => Or.inl h`,
   and `?link₂ := fun r x h => Or.inr h`.

The body goal of step 1 thus receives the hypothesis

```
(∃ h, r = () ∧ x = 1) ∨ (∃ h, r = () ∧ x = 2)
```

For a stateful program, `?H` also takes the states, and each payload equates them with the states
at its jump. In `StateM Nat`, the payload of `__do_jp () 1` in state `t` is
`fun r x s => ∃ (h : n > 0), r = () ∧ x = 1 ∧ s = t`.

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
  return some inst

/-- Register the join point `jp := val` that `wpLet?` introduced into `goal`. Returns `scope` with
`jp`, `goal` with `__do_jp_spec : ∀ xs, ⦃P xs⦄ jp xs ⦃post⦄`, and the body goal
`∀ xs, ⦃P xs⦄ val xs ⦃post⦄`, where `P xs = fun ss => ⌜?H xs ss⌝` over the states `ss` of `goal`. -/
public def registerJoinPoint (scope : Scope) (goal : MVarId) (jp : FVarId) (val : Expr)
    (info : WPApp) : VCGenM (Scope × List MVarId) := goal.withContext do
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
  let (hyp, pre, specTy, bodyTy, numStates) ← forallBoundedTelescope jpTy numParams fun xs _ => do
    let (hyp, P, numStates) ← forallBoundedTelescope info.Pred info.excessArgs.size fun ss B => do
      -- `?H` also takes the states, so that the body knows the state at each jump. Without a base
      -- instance for them, `?H` takes none and the body starts in an arbitrary state.
      let (ss, B, instB) ← match ← baseInstance? instCL ss with
        | some instB => pure (ss, B, instB)
        | none => pure (#[], info.Pred, instCL)
      let hypTy ← mkForallFVarsS (xs ++ ss) (mkSort .zero)
      let hyp ← mkFreshExprMVarAt lctx localInsts hypTy .syntheticOpaque
      let some u := (← Sym.getLevel B).dec | throwError "vcgen +jp: `{B}` is not a type"
      let φ ← mkAppNS hyp (xs ++ ss)
      let P ← mkLambdaFVarsS ss (← mkAppNS (mkConst ``CompleteLattice.ofProp [u]) #[B, instB, φ])
      return (hyp, P, ss.size)
    let triple (prog : Expr) : VCGenM Expr := do
      mkAppNS (mkConst ``Std.WP.Triple info.head.constLevels!)
        #[info.Pred, info.EPosts, info.Prog, info.Value, info.instAL, info.instEAL, prog,
          info.instWP, P, info.post, info.eposts]
    return (hyp.mvarId!, ← mkLambdaFVarsS xs P,
      ← mkForallFVarsS xs (← triple (← mkAppNS (.fvar jp) xs)),
      ← mkForallFVarsS xs (← triple (← betaS val xs)), numStates)
  let body ← mkFreshExprSyntheticOpaqueMVar bodyTy (← goal.getTag)
  let goal ← goal.replaceTargetDefEqFast (← mkLetS `__do_jp_spec specTy body (← goal.getType))
  let .goal decls goal ← Sym.introN goal 1
    | throwError "vcgen +jp: failed to introduce the proof of{indentExpr specTy}"
  let lctxSize := (← goal.getDecl).lctx.numIndices
  let joinPoint : JoinPoint := { spec := .fvar decls[0]!, pre, hyp, numStates, lctxSize }
  modify fun s => { s with joinPointBodies := s.joinPointBodies.insert body.mvarId! joinPoint }
  return ({ scope with joinPoints := scope.joinPoints.insert jp joinPoint }, [goal, body.mvarId!])

/-- The payload `fun xs => ∃ ys, xs = args` of a jump over the `locals` `ys`, and the witnesses of
its `∃`. Here `xs` and `args` include the states. A used `let` local stays a `let`. -/
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
        return mkApp2 (mkConst ``Exists [← Sym.getLevel decl.type]) decl.type
          (← mkLambdaFVars #[decl.toExpr] φ)
    return (← mkLambdaFVars xs body, (locals.filter (·.value?.isNone)).map (·.toExpr))

/-- A proof of `∃ ys, args = args` from the witnesses `ys`, by `rfl` on each equation. -/
private partial def mkPayloadProof (φ : Expr) (witnesses : List Expr) : MetaM Expr := do
  if let .letE _ _ v b _ := φ then
    return ← mkPayloadProof (b.instantiate1 v) witnesses
  match_expr φ with
  | Exists α p =>
    let w :: ws := witnesses | throwError "vcgen +jp: missing witness for{indentExpr φ}"
    return mkApp4 (mkConst ``Exists.intro φ.getAppFn.constLevels!) α p w
      (← mkPayloadProof (p.beta #[w]) ws)
  | And a b =>
    return mkApp4 (mkConst ``And.intro) a b
      (← mkPayloadProof a witnesses) (← mkPayloadProof b witnesses)
  | True => return mkConst ``True.intro
  | Eq α lhs _ => return mkApp2 (mkConst ``Eq.refl φ.getAppFn.constLevels!) α lhs
  | _ => throwError "vcgen +jp: unexpected payload{indentExpr φ}"

/-- Close the goal `pre ⊑ wp⟦jp args⟧ post eposts ss` of a jump to a join point of `scope` through
`pre ⊑ ⌜payload xs⌝ ⊑ ⌜?H xs⌝ ⊑ wp⟦jp args⟧ post eposts ss`, where `xs` includes the states of `?H`.
The first step holds by the jump's locals, the last is `__do_jp_spec args ss`, and the middle one
is a fresh `?link : ∀ xs, payload xs → ?H xs` that `finalizeJoinPoint` assigns. -/
public def jump? (scope : Scope) (goal : MVarId) (info : WPApp) :
    VCGenM (Option (List MVarId)) := do
  let some fv := info.prog.getAppFn.fvarId? | return none
  let some jp := scope.joinPoints.get? fv | return none
  goal.withContext do
  let args := info.prog.getAppArgs
  let ss := info.excessArgs
  unless jp.numStates ≤ ss.size do
    throwError "vcgen +jp: the jump{indentExpr info.prog}\nhas fewer than {jp.numStates} states"
  let xs := args ++ ss.extract 0 jp.numStates
  -- An implementation-detail hypothesis would become an `∃` binder, so it stays out of the payload.
  let locals := (← getLCtx).foldl (start := jp.lctxSize) (init := #[]) fun ds d =>
    if d.isImplementationDetail && d.value?.isNone then ds else ds.push d
  let (payload, witnesses) ← mkPayload jp xs locals
  let goalTy ← goal.getType
  let_expr PartialOrder.rel α inst pre rhs := goalTy
    | throwError "vcgen +jp: unexpected jump goal{indentExpr goalTy}"
  let lvls := goalTy.getAppFn.constLevels!
  -- `midH` is `ofProp L instL (?H xs) rest`, with `rest` the states outside `?H`.
  let midH ← betaS jp.pre (args ++ ss)
  let ofPropFn := midH.getAppFn
  let midArgs := midH.getAppArgs
  let L := midArgs[0]!
  let instL := midArgs[1]!
  let rest := midArgs.extract 3 midArgs.size
  let φ ← betaS payload xs
  let midP ← mkAppNS ofPropFn (#[L, instL, φ] ++ rest)
  let mut stateTys := #[]
  let mut LIt := L
  for _ in [:rest.size] do
    stateTys := stateTys.push LIt.bindingDomain!
    LIt := LIt.bindingBody!
  let constFn := stateTys.foldr (fun ty body => .lam `s ty body .default) pre
  let lvlL := ofPropFn.constLevels!
  let toPayload ← mkAppNS (mkConst ``le_ofProp lvlL)
    (#[L, instL, constFn, φ, ← mkPayloadProof φ witnesses.toList] ++ rest)
  let linkTy ← forallTelescope (← jp.hyp.getType) fun ys _ => do
    mkForallFVars ys (← mkArrow (payload.beta ys) (mkAppN (.mvar jp.hyp) ys))
  let link ← mkFreshExprSyntheticOpaqueMVar linkTy
  let toHyp ← mkAppNS (mkConst ``CompleteLattice.ofProp_mono lvlL)
    (#[L, instL, φ, midArgs[2]!, ← mkAppNS link xs] ++ rest)
  -- `Triple` is a structure whose one field is the `⊑ wp` entailment.
  let toWP ← mkAppNS (Expr.proj ``Std.WP.Triple 0 (← mkAppNS jp.spec args)) ss
  let relTrans := mkConst ``PartialOrder.rel_trans lvls
  let fromH ← mkAppNS relTrans #[α, inst, midP, midH, rhs, toHyp, toWP]
  goal.assign (← mkAppNS relTrans #[α, inst, pre, midP, rhs, toPayload, fromH])
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
