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
2. In the `then` branch, `jump?` closes the goal of `__do_jp () 1` with `__do_jp_spec () 1`, up to
   the goal `pre ⊑ ⌜?H () 1⌝`. It records the payload `fun r x => ∃ (h : n > 0), r = () ∧ x = 1`,
   which closes over the locals of the branch, here the condition `h`. The `else` branch records
   `fun r x => ∃ (h : ¬n > 0), r = () ∧ x = 2`.
3. `finalizeJoinPoints` sets `?H` to the disjunction of the two payloads. It proves
   `pre ⊑ ⌜?H () 1⌝` from the first disjunct, with the witness `h` and `rfl` for the equations.

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

/-- Register the join point `jp := val` that `wpLet?` introduced into `goal`. Returns `goal` with
`__do_jp_spec : ∀ xs, ⦃P xs⦄ jp xs ⦃post⦄`, and the body goal `∀ xs, ⦃P xs⦄ val xs ⦃post⦄`, where
`P xs = fun ss => ⌜?H xs ss⌝` over the states `ss` of `goal`. -/
public def registerJoinPoint (goal : MVarId) (jp : FVarId) (val : Expr) (info : WPApp) :
    VCGenM (List MVarId) := goal.withContext do
  let jpTy ← Sym.inferType (.fvar jp)
  let numParams ← Lean.Elab.Tactic.Do.getNumJoinParams jpTy info.Prog
  -- `Assertion` is a class abbreviation: `instAL` is `Assertion.mk instCL`, where `instCL` is the
  -- lattice instance of every elaborated `⌜·⌝`, or it is a local instance.
  let instCL ← match_expr info.instAL with
    | Std.WP.Assertion.mk _ instCL => pure instCL
    | _ =>
      let lvls := (← Sym.inferType info.instAL).getAppFn.constLevels!
      mkAppNS (mkConst ``Std.WP.Assertion.toCompleteLattice lvls) #[info.Pred, info.instAL]
  -- `?H` also takes the states, so that the body knows the state at each jump. Without a base
  -- instance for them, `?H` takes none and the body starts in an arbitrary state.
  let numStates ← forallBoundedTelescope info.Pred info.excessArgs.size fun ss _ => do
    return if ss.size == info.excessArgs.size && (← baseInstance? instCL ss).isSome then ss.size
      else 0
  let lctx ← getLCtx
  let localInsts ← getLocalInstances
  let (hyp, pre, specTy, bodyTy) ← forallBoundedTelescope jpTy numParams fun xs _ => do
    let (hyp, P) ← forallBoundedTelescope info.Pred numStates fun ss B => do
      let hypTy ← mkForallFVarsS (xs ++ ss) (mkSort .zero)
      let hyp ← mkFreshExprMVarAt lctx localInsts hypTy .syntheticOpaque
      let some instB ← baseInstance? instCL ss | unreachable!
      let some u := (← Sym.getLevel B).dec | throwError "vcgen +jp: `{B}` is not a type"
      let φ ← mkAppNS hyp (xs ++ ss)
      return (hyp, ← mkLambdaFVarsS ss (← mkAppNS (mkConst ``CompleteLattice.ofProp [u]) #[B, instB, φ]))
    let triple (prog : Expr) : VCGenM Expr := do
      mkAppNS (mkConst ``Std.WP.Triple info.head.constLevels!)
        #[info.Pred, info.EPosts, info.Prog, info.Value, info.instAL, info.instEAL, prog,
          info.instWP, P, info.post, info.eposts]
    return (hyp.mvarId!, ← mkLambdaFVarsS xs P,
      ← mkForallFVarsS xs (← triple (← mkAppNS (.fvar jp) xs)),
      ← mkForallFVarsS xs (← triple (← betaS val xs)))
  let body ← mkFreshExprSyntheticOpaqueMVar bodyTy (← goal.getTag)
  let goal ← goal.define `__do_jp_spec specTy body
  let .goal decls goal ← Sym.introN goal 1
    | throwError "vcgen +jp: failed to introduce the proof of{indentExpr specTy}"
  let lctxSize := (← goal.getDecl).lctx.numIndices
  modify fun s => { s with
    joinPoints := s.joinPoints.insert jp
      { spec := .fvar decls[0]!, pre, hyp, numStates, lctxSize } }
  return [goal, body.mvarId!]

/-- Throw if `payload` mentions a local introduced after registration, directly or through the
local context of a metavariable. `?H` and thus `payload` live in the context of registration. -/
private def checkPayloadScope (jp : JoinPoint) (jump payload : Expr) : MetaM Unit := do
  let lctx ← getLCtx
  let leakedRef ← IO.mkRef (#[] : Array Name)
  let note (decl : LocalDecl) : IO Unit := do
    if decl.index ≥ jp.lctxSize then leakedRef.modify (·.push decl.userName)
  payload.forEach fun sub => do
    match sub with
    | .fvar fvarId => if let some decl := lctx.find? fvarId then note decl
    | .mvar mvarId =>
      for decl? in (← mvarId.getDecl).lctx.decls.toList do
        if let some decl := decl? then note decl
    | _ => pure ()
  let leaked ← leakedRef.get
  unless leaked.isEmpty do
    throwError "vcgen +jp: the precondition of jump{indentExpr jump}\ndepends on \
      {leaked.toList}, which the join point's body cannot refer to"

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

/-- Close the goal `pre ⊑ wp⟦jp args⟧ post eposts ss` of a jump by `rel_trans` through
`__do_jp_spec args ss`, and record the goal `pre ⊑ ⌜?H args ss⌝` for `finalizeJoinPoints`. -/
public def jump? (goal : MVarId) (info : WPApp) : VCGenM (Option (List MVarId)) := do
  let some fv := info.prog.getAppFn.fvarId? | return none
  let some jp := (← get).joinPoints.get? fv | return none
  goal.withContext do
  let args := info.prog.getAppArgs
  let locals := (← getLCtx).foldl (start := jp.lctxSize) (init := #[]) fun ds d =>
    if d.isImplementationDetail then ds else ds.push d
  let ss := info.excessArgs
  unless jp.numStates ≤ ss.size do
    throwError "vcgen +jp: the jump{indentExpr info.prog}\nhas fewer than {jp.numStates} states"
  let (payload, witnesses) ← mkPayload jp (args ++ ss.extract 0 jp.numStates) locals
  checkPayloadScope jp info.prog payload
  let goalTy ← goal.getType
  let_expr PartialOrder.rel α inst pre rhs := goalTy
    | throwError "vcgen +jp: unexpected jump goal{indentExpr goalTy}"
  let lvls := goalTy.getAppFn.constLevels!
  -- `Triple` is a structure whose one field is the `⊑ wp` entailment.
  let specRel := Expr.proj ``Std.WP.Triple 0 (← mkAppNS jp.spec args)
  let mid ← betaS jp.pre (args ++ ss)
  let preGoal ← mkFreshExprSyntheticOpaqueMVar
    (← mkAppNS (mkConst ``PartialOrder.rel lvls) #[α, inst, pre, mid]) (← goal.getTag)
  goal.assign (← mkAppNS (mkConst ``PartialOrder.rel_trans lvls)
    #[α, inst, pre, mid, rhs, preGoal, ← mkAppNS specRel ss])
  let jump := { goal := preGoal.mvarId!, payload, witnesses }
  modify fun s => { s with jumps := s.jumps.insert fv ((s.jumps.getD fv #[]).push jump) }
  return some []

/-- The disjunction of `ps[lo:hi]`, balanced so that each disjunct has depth `O(log (hi - lo))`. -/
private partial def mkOrTree (ps : Array Expr) (lo hi : Nat) : Expr :=
  if hi == lo then mkConst ``False
  else if hi == lo + 1 then ps[lo]!
  else
    let mid := (lo + hi) / 2
    mkOr (mkOrTree ps lo mid) (mkOrTree ps mid hi)

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

/-- A proof of disjunct `i` of `φ = mkOrTree ps lo hi`. -/
private partial def mkDisjunctProof (φ : Expr) (i lo hi : Nat) (witnesses : List Expr) :
    MetaM Expr := do
  if hi == lo + 1 then
    return ← mkPayloadProof φ witnesses
  let_expr Or a b := φ | throwError "vcgen +jp: expected a disjunction{indentExpr φ}"
  let mid := (lo + hi) / 2
  if i < mid then
    return mkApp3 (mkConst ``Or.inl) a b (← mkDisjunctProof a i lo mid witnesses)
  else
    return mkApp3 (mkConst ``Or.inr) a b (← mkDisjunctProof b i mid hi witnesses)

/-- Close the goal `pre ⊑ ⌜φ⌝ ss` of jump `i` of `n` with `le_ofProp (fun _ => pre)`, applied to
disjunct `i` of `φ` and to the states `ss` outside `?H`. The kernel checks the result up to `β`. -/
private def dischargeJump (jump : Jump) (i n : Nat) : VCGenM Unit := jump.goal.withContext do
  let goalTy ← jump.goal.getType
  let_expr PartialOrder.rel _α _inst pre rhs := goalTy
    | throwError "vcgen +jp: unexpected jump goal{indentExpr goalTy}"
  let ofPropFn := rhs.getAppFn
  let rhsArgs := rhs.getAppArgs
  unless ofPropFn.isConstOf ``CompleteLattice.ofProp && rhsArgs.size ≥ 3 do
    throwError "vcgen +jp: the jump precondition is not a `⌜·⌝`{indentExpr rhs}"
  let L := rhsArgs[0]!
  let φ := rhsArgs[2]!
  let ss := rhsArgs.extract 3 rhsArgs.size
  let proof ← mkDisjunctProof (← instantiateMVarsS φ) i 0 n jump.witnesses.toList
  let mut stateTys := #[]
  let mut LIt := L
  for _ in [:ss.size] do
    stateTys := stateTys.push LIt.bindingDomain!
    LIt := LIt.bindingBody!
  let constFn := stateTys.foldr (fun ty body => .lam `s ty body .default) pre
  let base := mkAppN (mkConst ``le_ofProp ofPropFn.constLevels!)
    #[L, rhsArgs[1]!, constFn, φ, proof]
  jump.goal.assign (← mkAppNS base ss)

/-- Assign each `?H` the disjunction of its jumps' payloads, `False` if no jump reaches the join
point, and discharge the recorded goal of each jump. -/
public def finalizeJoinPoints : VCGenM Unit := do
  let s ← get
  for (fv, jp) in s.joinPoints do
    let jumps := s.jumps.getD fv #[]
    forallTelescope (← jp.hyp.getType) fun xs _ => do
      let φ := mkOrTree (jumps.map (·.payload.beta xs)) 0 jumps.size
      jp.hyp.assign (← mkLambdaFVars xs φ)
    for h : i in [:jumps.size] do
      dischargeJump jumps[i] i jumps.size

end Lean.Elab.Tactic.VCGen
