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
2. In the `then` branch, under the hypothesis `h₁ : n > 0`, `jump?` closes the goal
   `⊤ ⊑ wp⟦__do_jp () 1⟧ Q` with `__do_jp_spec () 1 ?pf₁` and records the jump. The `else` branch
   records the jump `__do_jp () 2` under `h₂ : ¬n > 0` with `?pf₂`.
3. `vcgen` reaches the body goal after all goals of the `if`, so both jumps are known by then.
   `finalizeJoinPoint` sets `?H` to the disjunction of the jumps, each over the locals of its
   branch and its arguments, `fun r x => (n > 0 ∧ r = () ∧ x = 1) ∨ (¬n > 0 ∧ r = () ∧ x = 2)`.
   It proves `?pf₁ := Or.inl ⟨h₁, rfl, rfl⟩` and `?pf₂ := Or.inr ⟨h₂, rfl, rfl⟩`. Jumps under a
   common local share its binder: the jumps of an `else if` chain share the conditions above them.

The body goal of step 1 thus receives the hypothesis

```
(n > 0 ∧ r = () ∧ x = 1) ∨ (¬n > 0 ∧ r = () ∧ x = 2)
```

For a stateful program, `?H` also takes the states, and each disjunct equates them with the states
at its jump. In `StateM Nat`, the disjunct of `__do_jp () 1` in state `t` is
`n > 0 ∧ r = () ∧ x = 1 ∧ s = t`.

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
      let rel ← mkAppNS (mkConst ``PartialOrder.rel goalTy.getAppFn.constLevels!)
        #[α, inst, top, wp]
      mkForallFVarsS (xs ++ ss) (← mkForallS `h .default (← mkAppNS hyp (xs ++ ss)) rel)
    return some (hyp.mvarId!, top, ← entails (← mkAppNS (.fvar jp) xs), ← entails (← betaS val xs))
    | return none
  let body ← mkFreshExprSyntheticOpaqueMVar bodyTy (← goal.getTag)
  let goal ← goal.replaceTargetDefEqFast (← mkLetS `__do_jp_spec specTy body goalTy)
  let .goal decls goal ← Sym.introN goal 1
    | throwError "vcgen +jp: failed to introduce the proof of{indentExpr specTy}"
  let joinPoint : JoinPoint :=
    { spec := .fvar decls[0]!, top, hyp, body := body.mvarId!, numStates := info.excessArgs.size }
  modify fun s => { s with
    pendingJoinPoints := s.pendingJoinPoints.insert joinPoint.body (joinPoint, #[]) }
  let scope := { scope with joinPoints := scope.joinPoints.insert jp joinPoint }
  return some (scope, [goal, joinPoint.body])

/-- Close the goal `⊤ ⊑ wp⟦jp args⟧ post eposts ss` of a jump to a join point of `scope` with
`__do_jp_spec args ss ?pf`, where `finalizeJoinPoint` assigns `?pf : ?H args ss`. A jump with a
precondition other than `⊤` unfolds `jp` instead. -/
public def jump? (scope : Scope) (goal : MVarId) (info : WPApp) :
    VCGenM (Option (List MVarId)) := do
  let some fv := info.prog.getAppFn.fvarId? | return none
  let some jp := scope.joinPoints.get? fv | return none
  goal.withContext do
  let_expr PartialOrder.rel _ _ pre _ := (← goal.getType) | return none
  unless pre == jp.top do return none
  unless info.excessArgs.size == jp.numStates do
    throwError "vcgen +jp: the jump{indentExpr info.prog}\ndoes not have {jp.numStates} states"
  let args := info.prog.getAppArgs ++ info.excessArgs
  let pf ← mkFreshExprSyntheticOpaqueMVar (← mkAppNS (.mvar jp.hyp) args)
  goal.assign (← mkAppNS jp.spec (args.push pf))
  modify fun s => { s with
    pendingJoinPoints := s.pendingJoinPoints.modify jp.body fun (jp, jumps) =>
      (jp, jumps.push { pf := pf.mvarId!, args }) }
  return some []

/-- The locals of `jump` after `__do_jp_spec`. -/
private def jumpLocals (jp : JoinPoint) (jump : Jump) : MetaM (Array LocalDecl) := do
  let lctx := (← jump.pf.getDecl).lctx
  let start := (lctx.get! jp.spec.fvarId!).index + 1
  -- An implementation-detail hypothesis would become an `∃` binder, so it stays out of `?H`.
  return lctx.foldl (start := start) (init := #[]) fun ds d =>
    if d.isImplementationDetail && d.value?.isNone then ds else ds.push d

/-- `φ` under the local `d`: a `let` for a `let` local, a conjunct `d.type ∧ φ` for a hypothesis
that `φ` does not depend on, and `∃ d, φ` otherwise. -/
private def bindLocal (d : LocalDecl) (φ : Expr) : VCGenM Expr := do
  -- `mkLambdaFVars`/`mkLetFVars` re-scope a metavariable whose local context contains `d`, such as
  -- the invariant of a loop in the branch.
  if d.value?.isSome then
    return ← mkLetFVars #[d.toExpr] φ (generalizeNondepLet := false)
  let lam ← mkLambdaFVars #[d.toExpr] φ
  -- A conjunct needs no instantiation in its proof, where each `∃` copies the rest.
  if (← Sym.inferType d.type).isProp && !lam.bindingBody!.hasLooseBVars then
    return mkAnd d.type lam.bindingBody!
  return mkApp2 (mkConst ``Exists [← Sym.getLevel d.type]) d.type lam

/-- The disjunction of `ps[lo:hi]`, balanced so that each disjunct has depth `O(log (hi - lo))`. -/
private partial def mkOrTree (ps : Array Expr) (lo hi : Nat) : Expr :=
  if hi == lo then mkConst ``False
  else if hi == lo + 1 then ps[lo]!
  else
    let mid := (lo + hi) / 2
    mkOr (mkOrTree ps lo mid) (mkOrTree ps mid hi)

/-- A proof of `φ = mkOrTree ps lo hi` from the proof `k ps[i]` of its disjunct `ps[i]`. -/
private partial def mkOrIntro (φ : Expr) (i lo hi : Nat) (k : Expr → MetaM Expr) : MetaM Expr := do
  if hi == lo + 1 then
    return ← k φ
  let_expr Or a b := φ | throwError "vcgen +jp: expected a disjunction{indentExpr φ}"
  let mid := (lo + hi) / 2
  if i < mid then
    return mkApp3 (mkConst ``Or.inl) a b (← mkOrIntro a i lo mid k)
  else
    return mkApp3 (mkConst ``Or.inr) a b (← mkOrIntro b i mid hi k)

/-- The trie of the `jumps` from local `i` on, over the parameters `xs` of `?H`. Its disjuncts bind
each distinct local `i` of the jumps above the trie of the jumps that share it, and give the
equations `xs = args` of each jump without local `i`. Returns the path of each jump, the index and
number of the disjuncts it passes. -/
private partial def mkTrie (xs : Array Expr) (jumps : Array (Jump × Array LocalDecl)) (i : Nat) :
    VCGenM (Expr × Array (List (Nat × Nat))) := do
  let mut groups : Array (Array Nat) := #[]
  let mut byLocal : Std.HashMap FVarId Nat := {}
  for h : k in [:jumps.size] do
    if let some d := jumps[k].2[i]? then
      if let some g := byLocal[d.fvarId]? then
        groups := groups.modify g (·.push k)
        continue
      byLocal := byLocal.insert d.fvarId groups.size
    groups := groups.push #[k]
  let mut disjuncts := #[]
  let mut paths := Array.replicate jumps.size []
  for h : g in [:groups.size] do
    let ks := groups[g]
    let (jump, locals) := jumps[ks[0]!]!
    let (disjunct, subPaths) ← match locals[i]? with
      | some d =>
        let (φ, subPaths) ← mkTrie xs (ks.map (jumps[·]!)) (i + 1)
        let decl ← jump.pf.getDecl
        pure (← withLCtx decl.lctx decl.localInstances (bindLocal d φ), subPaths)
      | none =>
        let eqs ← xs.mapIdxM fun j x => do
          let α ← Sym.inferType x
          return mkApp3 (mkConst ``Eq [← Sym.getLevel α]) α x jump.args[j]!
        pure (mkAndN eqs.toList, #[[]])
    disjuncts := disjuncts.push disjunct
    for (k, path) in ks.zip subPaths do
      paths := paths.set! k ((g, groups.size) :: path)
  return (mkOrTree disjuncts 0 disjuncts.size, paths)

/-- A proof of the equations `args = args`, by `rfl` on each. -/
private partial def mkEqsProof (φ : Expr) : MetaM Expr := do
  match_expr φ with
  | And a b => return mkApp4 (mkConst ``And.intro) a b (← mkEqsProof a) (← mkEqsProof b)
  | True => return mkConst ``True.intro
  | Eq α lhs _ => return mkApp2 (mkConst ``Eq.refl φ.getAppFn.constLevels!) α lhs
  | _ => throwError "vcgen +jp: unexpected equations{indentExpr φ}"

/-- A proof of `φ`, a trie of `mkTrie` at the arguments of a jump, along the `path` of the jump,
from the witnesses `ws` of its `∃`s and its conjuncts. -/
private partial def mkTrieProof (φ : Expr) (path : List (Nat × Nat)) (ws : List Expr) :
    MetaM Expr := do
  let (g, n) :: path := path | throwError "vcgen +jp: empty path into{indentExpr φ}"
  mkOrIntro φ g 0 n fun φ => do
    if path.isEmpty then
      return ← mkEqsProof φ
    if let .letE _ _ v b _ := φ then
      return ← mkTrieProof (b.instantiate1 v) path ws
    let w :: ws := ws | throwError "vcgen +jp: missing witness for{indentExpr φ}"
    match_expr φ with
    | Exists α p =>
      return mkApp4 (mkConst ``Exists.intro φ.getAppFn.constLevels!) α p w
        (← mkTrieProof (p.beta #[w]) path ws)
    | And a b => return mkApp4 (mkConst ``And.intro) a b w (← mkTrieProof b path ws)
    | _ => throwError "vcgen +jp: unexpected binder{indentExpr φ}"

/-- Assign `?H` of `jp` the trie of its `jumps`, `False` if no jump reaches `jp`, and each jump's
`?pf` the proof along its path. `vcgen` processes the body goal of `jp` after all goals below the
registration, so every jump is known by then. -/
public def finalizeJoinPoint (jp : JoinPoint) (jumps : Array Jump) : VCGenM Unit := do
  let jumps ← jumps.mapM fun jump => return (jump, ← jumpLocals jp jump)
  let paths ← forallTelescope (← jp.hyp.getType) fun xs _ => do
    let (φ, paths) ← mkTrie xs jumps 0
    jp.hyp.assign (← mkLambdaFVars xs φ)
    return paths
  for ((jump, locals), path) in jumps.zip paths do
    jump.pf.withContext do
      let witnesses := (locals.filter (·.value?.isNone)).map (·.toExpr)
      jump.pf.assign (← mkTrieProof (← instantiateMVars (← jump.pf.getType)) path witnesses.toList)

end Lean.Elab.Tactic.VCGen
