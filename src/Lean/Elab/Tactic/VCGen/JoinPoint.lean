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
import Lean.Meta.Sym.MaxFVar
import Lean.Meta.Sym.ExprPtr
import Lean.Elab.Tactic.VCGen.Util
import Lean.Elab.Tactic.VCGen.Reduce

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

The join RHS `fun r x => pure (x + 1)` is the shared code, and the join body `if n > 0 then …`
jumps to it. Without `+jp`, `vcgen` unfolds `__do_jp` at each jump, so `k` consecutive splits give
`2ᵏ` copies of the join RHS. With `+jp`, `vcgen` takes three steps:

1. `registerJoinPoint` creates `?H : Unit → Nat → Prop` and binds
   `__do_jp_spec : ∀ r x, ?H r x → ⊤ ⊑ wp⟦__do_jp r x⟧ Q` in the goal of the `if`. It adds the goal
   `∀ r x, ?H r x → ⊤ ⊑ wp⟦pure (x + 1)⟧ Q` for the join RHS.
2. In the `then` branch, under the hypothesis `h₁ : n > 0`, `wpJump?` closes the goal
   `⊤ ⊑ wp⟦__do_jp () 1⟧ Q` with `__do_jp_spec () 1 ?pf₁` and records the jump. The `else` branch
   records the jump `__do_jp () 2` under `h₂ : ¬n > 0` with `?pf₂`.
3. `vcgen` reaches the RHS goal after all goals of the join body, so both jumps are known by then.
   `finalizeJoinPoint` anti-unifies the arguments of the jumps for each parameter other than
   `r : Unit`, and states the anti-unifier above a disjunction with one disjunct per jump over the
   locals of its branch. The arguments `1` and `2` of `x` have no common part, so the disjuncts
   give the values of `x`: `fun r x => (n > 0 ∧ x = 1) ∨ (¬n > 0 ∧ x = 2)`. It proves
   `?pf₁ := Or.inl ⟨h₁, rfl⟩` and `?pf₂ := Or.inr ⟨h₂, rfl⟩`. Jumps under a common local share its
   binder: the jumps of an `else if` chain share the conditions above them.

The RHS goal of step 1 thus receives the hypothesis

```
(n > 0 ∧ x = 1) ∨ (¬n > 0 ∧ x = 2)
```

This `?H` is the strongest postcondition of the join body at its jumps to `__do_jp`, over the join
parameters `r` and `x`.

For a stateful program, `?H` also takes the states. In `StateM Nat`, with both jumps in the state
`t`, it is `s = t ∧ ((n > 0 ∧ x = 1) ∨ (¬n > 0 ∧ x = 2))`: the equation `s = t` holds at every jump,
so it stands above the disjunction. The section on anti-unification below gives the general rule.
-/

/-- The lattice instance of `B`, for `Pred = ∀ s₁ … sₙ, B` and the states `ss = #[s₁, …, sₙ]`,
read off the instance `instCL` of `Pred`, which nests one `instCompleteLatticePi` per state. -/
def baseInstance? (instCL : Expr) (ss : Array Expr) : SymM (Option Expr) := do
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
`__do_jp_spec : ∀ xs ss, ?H xs ss → ⊤ ⊑ wp⟦jp xs⟧ post eposts ss`, and the goal
`∀ xs ss, ?H xs ss → ⊤ ⊑ wp⟦val xs⟧ post eposts ss` for the join RHS `val`. Returns `none` if
`jp` is no `__do_jp` with a lambda RHS under `+jp`, or if the states have no base lattice
instance. -/
public def registerJoinPoint (scope : Scope) (goal : MVarId) (jp : FVarId) (val : Expr)
    (info : WPApp) : VCGenM (Option (Scope × List MVarId)) := goal.withContext do
  unless (← read).useJP && Lean.Elab.Tactic.Do.isJP (← jp.getUserName) && val.isLambda do
    return none
  let goalTy ← goal.getType
  let_expr PartialOrder.rel α inst _ _ := goalTy | return none
  let jpFVar ← mkFVarS jp
  let jpTy ← Sym.inferType jpFVar
  let numParams ← Lean.Elab.Tactic.Do.getNumJoinParams jpTy info.Prog
  -- `Assertion` is a class abbreviation: `instAL` is `Assertion.mk instCL`, where `instCL` is the
  -- lattice instance of every elaborated `⌜·⌝`, or it is a local instance.
  let instCL ← match_expr info.instAL with
    | Std.WP.Assertion.mk _ instCL => pure instCL
    | _ =>
      let lvls := (← Sym.inferType info.instAL).getAppFn.constLevels!
      mkAppNS (← mkConstS ``Std.WP.Assertion.toCompleteLattice lvls) #[info.Pred, info.instAL]
  let lctx ← getLCtx
  let localInsts ← getLocalInstances
  let some (hyp, top, specTy, rhsTy) ← forallBoundedTelescope jpTy numParams fun xs _ => do
      forallBoundedTelescope info.Pred info.excessArgs.size fun ss B => do
    let xs ← xs.mapM (share ·)
    let ss ← ss.mapM (share ·)
    let B ← share B
    let some instB ← baseInstance? instCL ss | return none
    let some u := (← Sym.getLevel B).dec | throwError "vcgen +jp: `{B}` is not a type"
    let top ← mkAppNS (← mkConstS ``Lean.Order.top [u]) #[B, instB]
    let hyp ← share (← mkFreshExprMVarAt lctx localInsts
      (← mkForallFVarsS (xs ++ ss) (← mkSortS .zero)) .syntheticOpaque)
    let entails (prog : Expr) : VCGenM Expr := do
      let wp ← mkAppNS (← mkAppNS info.head (info.args.set! 7 prog)) ss
      let rel ← mkAppNS (← mkConstS ``PartialOrder.rel goalTy.getAppFn.constLevels!)
        #[α, inst, top, wp]
      mkForallFVarsS (xs ++ ss) (← mkForallS `h .default (← mkAppNS hyp (xs ++ ss)) rel)
    return some (hyp.mvarId!, top, ← entails (← mkAppNS jpFVar xs), ← entails (← betaS val xs))
    | return none
  let rhs ← share (← mkFreshExprSyntheticOpaqueMVar rhsTy (← goal.getTag))
  let goal ← goal.replaceTargetDefEqFast (← mkLetS `__do_jp_spec specTy rhs goalTy)
  let .goal decls goal ← Sym.introN goal 1
    | throwError "vcgen +jp: failed to introduce the proof of{indentExpr specTy}"
  let spec ← mkFVarS decls[0]!
  let joinPoint : JoinPoint :=
    { spec, top, hyp, rhsGoal := rhs.mvarId!, numStates := info.excessArgs.size }
  modify fun s => { s with
    pendingJoinPoints := s.pendingJoinPoints.insert joinPoint.rhsGoal (joinPoint, #[]) }
  let scope := { scope with joinPoints := scope.joinPoints.insert jp joinPoint }
  return some (scope, [goal, joinPoint.rhsGoal])

/-- Close the goal `⊤ ⊑ wp⟦jp args⟧ post eposts ss` of a jump to a join point of `scope` with
`__do_jp_spec args ss ?pf`, where `finalizeJoinPoint` assigns `?pf : ?H args ss`. A jump with a
precondition other than `⊤` unfolds `jp` instead. -/
public def wpJump? (scope : Scope) (goal : MVarId) (info : WPApp) :
    VCGenM (Option (List MVarId)) := do
  let some fv := info.prog.getAppFn.fvarId? | return none
  let some jp := scope.joinPoints.get? fv | return none
  goal.withContext do
  let_expr PartialOrder.rel _ _ pre _ := (← goal.getType) | return none
  unless pre == jp.top do return none
  unless info.excessArgs.size == jp.numStates do
    throwError "vcgen +jp: the jump{indentExpr info.prog}\ndoes not have {jp.numStates} states"
  let args ← (info.prog.getAppArgs ++ info.excessArgs).mapM (reduceHead ·)
  let pf ← share (← mkFreshExprSyntheticOpaqueMVar (← mkAppNS (← mkMVarS jp.hyp) args))
  goal.assign (← mkAppNS jp.spec (args.push pf))
  modify fun s => { s with
    pendingJoinPoints := s.pendingJoinPoints.modify jp.rhsGoal fun (jp, jumps) =>
      (jp, jumps.push { proof := pf.mvarId!, args }) }
  return some []

/-- The locals of `jump` after `__do_jp_spec`. -/
def jumpLocals (jp : JoinPoint) (jump : Jump) : MetaM (Array LocalDecl) := do
  let lctx := (← jump.proof.getDecl).lctx
  let start := (lctx.get! jp.spec.fvarId!).index + 1
  -- An implementation-detail hypothesis would become an `∃` binder, so it stays out of `?H`.
  return lctx.foldl (start := start) (init := #[]) fun ds d =>
    if d.isImplementationDetail && d.value?.isNone then ds else ds.push d

/-- `φ` under the local `d`: a `let` for a `let` local, a conjunct `d.type ∧ φ` for a hypothesis
that `φ` does not depend on, and `∃ d, φ` otherwise. -/
def bindLocal (d : LocalDecl) (φ : Expr) : VCGenM Expr := do
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
partial def mkOrTree (ps : Array Expr) (lo hi : Nat) : Expr :=
  if hi == lo then mkConst ``False
  else if hi == lo + 1 then ps[lo]!
  else
    let mid := (lo + hi) / 2
    mkOr (mkOrTree ps lo mid) (mkOrTree ps mid hi)

/-- A proof of `φ = mkOrTree ps lo hi` from the proof `k ps[i]` of its disjunct `ps[i]`. -/
partial def mkOrIntro (φ : Expr) (i lo hi : Nat) (k : Expr → MetaM Expr) : MetaM Expr := do
  if hi == lo + 1 then
    return ← k φ
  let_expr Or a b := φ | throwError "vcgen +jp: expected a disjunction{indentExpr φ}"
  let mid := (lo + hi) / 2
  if i < mid then
    return mkApp3 (mkConst ``Or.inl) a b (← mkOrIntro a i lo mid k)
  else
    return mkApp3 (mkConst ``Or.inr) a b (← mkOrIntro b i mid hi k)

/-- The trie of the `jumps` from local `i` on. Its disjuncts bind each distinct local `i` of the
jumps above the trie of the jumps that share it, and end in the leaf of each jump without local
`i`. Returns the path of each jump, the index and number of the disjuncts it passes. -/
partial def mkTrie (jumps : Array (Jump × Array LocalDecl × Expr)) (i : Nat) :
    VCGenM (Expr × Array (List (Nat × Nat))) := do
  let mut groups : Array (Array Nat) := #[]
  let mut byLocal : Std.HashMap FVarId Nat := {}
  for h : k in [:jumps.size] do
    if let some d := jumps[k].2.1[i]? then
      if let some g := byLocal[d.fvarId]? then
        groups := groups.modify g (·.push k)
        continue
      byLocal := byLocal.insert d.fvarId groups.size
    groups := groups.push #[k]
  let mut disjuncts := #[]
  let mut paths := Array.replicate jumps.size []
  for h : g in [:groups.size] do
    let ks := groups[g]
    let (jump, locals, leaf) := jumps[ks[0]!]!
    let (disjunct, subPaths) ← match locals[i]? with
      | some d =>
        let (φ, subPaths) ← mkTrie (ks.map (jumps[·]!)) (i + 1)
        let decl ← jump.proof.getDecl
        pure (← withLCtx decl.lctx decl.localInstances (bindLocal d φ), subPaths)
      | none => pure (leaf, #[[]])
    disjuncts := disjuncts.push disjunct
    for (k, path) in ks.zip subPaths do
      paths := paths.set! k ((g, groups.size) :: path)
  return (mkOrTree disjuncts 0 disjuncts.size, paths)

/-!
## Anti-unification of the jump arguments

In `StateM S` with `structure S where pc : Nat; r : Nat`, the jumps of a join point after
`if c then modify f else modify g` pass the states

```
t₁ := { pc := s.pc + 4, r := s.r + 1 }
t₂ := { pc := s.pc + 4, r := s.r + 2 }
```

The anti-unifier of `t₁` and `t₂` is `{ pc := s.pc + 4, r := s.r + z }`, with the hole `z` taking
the value `1` at the first jump and `2` at the second. The join hypothesis `?H` states the
anti-unifier once, above the trie of the jumps, and the leaf of each jump gives the values of the
holes:

```
fun _ s' => ∃ z, s' = { pc := s.pc + 4, r := s.r + z } ∧ ((c ∧ z = 1) ∨ (¬c ∧ z = 2))
```

Thus `s'.pc = s.pc + 4` follows from `?H` without a case split. A parameter `x` whose anti-unifier
is a hole `z` takes the place of `z`: `?H` has no equation `x = z` and no binder `∃ z`, and the
leaves give the values of `x`.
-/

/-- A hole of the anti-unifier, with the placeholder `fvarId : type` and the value `vals[k]` at
jump `k`. -/
structure Hole where
  fvarId : FVarId
  type : Expr
  vals : Array Expr

structure AUState where
  holes : Array Hole := #[]
  /-- The anti-unifier of each tuple of subterms, `none` if it has none. -/
  cache : Std.HashMap (Array ExprPtr) (Option Expr) := {}

abbrev AUM := StateRefT AUState VCGenM

/-- `e` mentions only locals with an index below `cutoff`, the locals common to all jumps. -/
def isCommon (cutoff : Nat) (e : Expr) : AUM Bool := do
  let some fvarId ← getMaxFVar? e | return true
  let some d := (← getLCtx).find? fvarId | return false
  return d.index < cutoff

/-- The positions of `fn` applied to `n` arguments at which a hole breaks the type of the
application: the instances, and the arguments that a later argument or the result type depends
on. -/
def rigidArgs (fn : Expr) (n : Nat) : MetaM (Array Bool) := do
  let info ← getFunInfoNArgs fn n
  let mut rigid := info.paramInfo.map fun p => p.hasFwdDeps || p.isInstImplicit
  for i in info.resultDeps do
    rigid := rigid.setIfInBounds i true
  return rigid

/-- A hole with the values `ts` at the jumps, of type `type?` or the type of `ts[0]`. Returns
`none` if the type mentions a local of a branch. -/
def mkHole (cutoff : Nat) (ts : Array Expr) (type? : Option Expr := none) :
    AUM (Option Expr) := do
  let type ← match type? with
    | some type => pure type
    | none => Sym.inferType ts[0]!
  unless ← isCommon cutoff type do return none
  let fvarId ← mkFreshFVarId
  modify fun s => { s with holes := s.holes.push { fvarId, type, vals := ts } }
  return some (← mkFVarS fvarId)

mutual

/-- The anti-unifier of the subterms `ts` at one position of the jump arguments. Subterms that are
one pointer stay, unless they mention a local of a branch. Applications of one function to the
same number of arguments are anti-unified argument by argument, if they differ only at positions
that are not rigid. All other subterms become a hole. Returns `none` if a hole has a type that
mentions a local of a branch. -/
partial def antiUnify (cutoff : Nat) (ts : Array Expr) : AUM (Option Expr) := do
  let key := ts.map ({ expr := · })
  if let some r := (← get).cache[key]? then return r
  let r ← antiUnifyCore cutoff ts
  modify fun s => { s with cache := s.cache.insert key r }
  return r

partial def antiUnifyCore (cutoff : Nat) (ts : Array Expr) : AUM (Option Expr) := do
  let t := ts[0]!
  if ts.all (isSameExpr t ·) && (← isCommon cutoff t) then return some t
  let fn := t.getAppFn
  let n := t.getAppNumArgs
  if n > 0 && ts.all (fun s => isSameExpr s.getAppFn fn && s.getAppNumArgs == n) then
    if ← isCommon cutoff fn then
      let saved ← get
      let rigid ← rigidArgs fn n
      let argss := ts.map (·.getAppArgs)
      let mut args := Array.mkEmpty n
      let mut ok := true
      for i in [:n] do
        let ai := argss.map (·[i]!)
        let a := ai[0]!
        if ai.all (isSameExpr a ·) && (← isCommon cutoff a) then
          args := args.push a
        else if rigid[i]?.getD true then
          ok := false
          break
        else if let some a ← antiUnify cutoff ai then
          args := args.push a
        else
          ok := false
          break
      if ok then return some (← mkAppNS fn args)
      set saved
  mkHole cutoff ts

end

/-- The anti-unifier of the arguments of `jumps` for the parameters `xs` of `?H`. Returns the
equations `x = g` for the parameters `x` whose anti-unifier `g` is not a hole, the holes that
remain, and the leaf of each jump, which equates each hole or parameter with its value at that
jump. The parameters of type `PUnit`, such as the result `__r` of a `Unit` statement, get no
equation. -/
def antiUnifyJumps (jp : JoinPoint) (xs : Array Expr) (jumps : Array Jump) :
    VCGenM (Array Expr × Array Hole × Array Expr) := do
  let some jump₀ := jumps[0]? | return (#[], #[], #[])
  let types ← xs.mapM (Sym.inferType ·)
  let decl₀ ← jump₀.proof.getDecl
  let cutoff := (decl₀.lctx.get! jp.spec.fvarId!).index + 1
  let go : AUM (Array (Option Expr)) := do
    let mut gs := #[]
    for h : j in [:xs.size] do
      if types[j]!.isConstOf ``PUnit then
        gs := gs.push none
        continue
      let ts := jumps.map (·.args[j]!)
      if let some g ← antiUnify cutoff ts then
        gs := gs.push (some g)
      else
        let some z ← mkHole cutoff ts types[j]!
          | throwError "vcgen +jp: the parameter{indentExpr xs[j]}\nhas a type with a local of a branch"
        gs := gs.push (some z)
    return gs
  let (gs, st) ← withLCtx decl₀.lctx decl₀.localInstances (go.run {})
  -- A parameter takes the place of the hole that is its anti-unifier.
  let mut param : Std.HashMap FVarId Expr := {}
  for h : j in [:gs.size] do
    if let some (.fvar z) := gs[j] then
      if st.holes.any (·.fvarId == z) && !param.contains z then
        param := param.insert z xs[j]!
  let holes := st.holes.filter (!param.contains ·.fvarId)
  let substitution := param.toArray
  let fromHoles := substitution.map (mkFVar ·.1)
  let toParams := substitution.map (·.2)
  let mut eqs := #[]
  for h : j in [:gs.size] do
    let some g := gs[j] | continue
    if let .fvar z := g then
      if param[z]?.any (isSameExpr · xs[j]!) then continue
    let g := g.replaceFVars fromHoles toParams
    eqs := eqs.push (mkApp3 (mkConst ``Eq [← Sym.getLevel types[j]!]) types[j]! xs[j]! g)
  let leaves ← (Array.range jumps.size).mapM fun k => do
    let eqs ← st.holes.mapM fun h => do
      let lhs := param[h.fvarId]?.getD (mkFVar h.fvarId)
      return mkApp3 (mkConst ``Eq [← Sym.getLevel h.type]) h.type lhs h.vals[k]!
    return mkAndN eqs.toList
  return (eqs, holes, leaves)

/-- A proof of the equations `args = args`, by `rfl` on each. -/
partial def mkEqsProof (φ : Expr) : MetaM Expr := do
  match_expr φ with
  | And a b => return mkApp4 (mkConst ``And.intro) a b (← mkEqsProof a) (← mkEqsProof b)
  | True => return mkConst ``True.intro
  | Eq α lhs _ => return mkApp2 (mkConst ``Eq.refl φ.getAppFn.constLevels!) α lhs
  | _ => throwError "vcgen +jp: unexpected equations{indentExpr φ}"

/-- A proof of `φ`, a trie of `mkTrie` at the arguments of a jump, along the `path` of the jump,
whose `locals` witness its `∃`s and its conjuncts. -/
partial def mkTrieProof (φ : Expr) (path : List (Nat × Nat)) (locals : List LocalDecl) :
    MetaM Expr := do
  let (g, n) :: path := path | throwError "vcgen +jp: empty path into{indentExpr φ}"
  mkOrIntro φ g 0 n fun φ => do
    if path.isEmpty then
      return ← mkEqsProof φ
    let d :: locals := locals | throwError "vcgen +jp: missing local for{indentExpr φ}"
    if d.value?.isSome then
      -- `bindLocal` drops a `let` that the rest of `φ` does not use.
      let .letE _ _ v b _ := φ | return ← mkTrieProof φ path locals
      return ← mkTrieProof (b.instantiate1 v) path locals
    let w := d.toExpr
    match_expr φ with
    | Exists α p =>
      return mkApp4 (mkConst ``Exists.intro φ.getAppFn.constLevels!) α p w
        (← mkTrieProof (p.beta #[w]) path locals)
    | And a b => return mkApp4 (mkConst ``And.intro) a b w (← mkTrieProof b path locals)
    | _ => throwError "vcgen +jp: unexpected binder{indentExpr φ}"

/-- A proof of `φ`, the join hypothesis `?H` at the arguments of jump `k`: the values of `holes` at
`k` witness the `∃`s, `rfl` proves the equations if `hasEqs`, and the `path` of the jump leads
through the trie. -/
partial def mkJumpProof (φ : Expr) (holes : List Hole) (k : Nat) (hasEqs : Bool)
    (path : List (Nat × Nat)) (locals : List LocalDecl) : MetaM Expr := do
  match holes with
  | h :: holes =>
    let_expr Exists α p := φ | throwError "vcgen +jp: expected `∃`{indentExpr φ}"
    let w := h.vals[k]!
    return mkApp4 (mkConst ``Exists.intro φ.getAppFn.constLevels!) α p w
      (← mkJumpProof (p.beta #[w]) holes k hasEqs path locals)
  | [] =>
    unless hasEqs do return ← mkTrieProof φ path locals
    let_expr And a b := φ | throwError "vcgen +jp: expected `∧`{indentExpr φ}"
    return mkApp4 (mkConst ``And.intro) a b (← mkEqsProof a) (← mkTrieProof b path locals)

/-- Assign `?H` of `jp` the anti-unifier of the arguments of its `jumps` above the trie of the
jumps, `False` if no jump reaches `jp`, and each jump's `?pf` its proof. `vcgen` processes the RHS
goal of `jp` after all goals below the registration, so every jump is known by then. -/
public def finalizeJoinPoint (jp : JoinPoint) (jumps : Array Jump) : VCGenM Unit := do
  let jumpsLocals ← jumps.mapM fun jump => return (jump, ← jumpLocals jp jump)
  let (paths, holes, hasEqs) ← forallTelescope (← jp.hyp.getType) fun xs _ => do
    let (eqs, holes, leaves) ← antiUnifyJumps jp xs jumps
    let jumps := (jumpsLocals.zip leaves).map fun ((jump, locals), leaf) => (jump, locals, leaf)
    let (trie, paths) ← mkTrie jumps 0
    let lctx := holes.foldl (init := ← getLCtx) fun lctx h => lctx.mkLocalDecl h.fvarId `z h.type
    let φ ← withLCtx lctx (← getLocalInstances) do
      let body := if eqs.isEmpty then trie else mkAnd (mkAndN eqs.toList) trie
      holes.foldrM (init := body) fun h φ => do
        return mkApp2 (mkConst ``Exists [← Sym.getLevel h.type]) h.type
          (← mkLambdaFVars #[mkFVar h.fvarId] φ)
    jp.hyp.assign (← mkLambdaFVars xs φ)
    return (paths, holes, !eqs.isEmpty)
  for h : k in [:jumpsLocals.size] do
    let (jump, locals) := jumpsLocals[k]
    jump.proof.withContext do
      let φ ← instantiateMVars (← jump.proof.getType)
      jump.proof.assign (← mkJumpProof φ holes.toList k hasEqs paths[k]! locals.toList)

end Lean.Elab.Tactic.VCGen
