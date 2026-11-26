/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Elab.Tactic.VCGen.Context
import Lean.Elab.Tactic.VCGen.Simp
public import Lean.Elab.Tactic.VCGen.WPApp
import Lean.Meta.Sym.InferType
import Lean.Meta.Sym.SynthInstance
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

A join point is a local function whose every use is a jump in tail position. The do-elaborator
shares the code after an `if` or a `match` through a join point, and a program or a specification
can share a continuation through one. This module lets `vcgen +jp` prove the shared code once
instead of once per jump. For example,

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
   For each parameter other than `r : Unit`, `finalizeJoinPoint` computes the common part of its
   arguments at the jumps, with a hole `z` where they differ. It states the equations of the
   parameters with their common parts above a disjunction with one disjunct per jump, which binds
   the locals of the branch and gives the values of the holes. The arguments `1` and `2` of `x`
   have no common part, so the disjuncts give the values of `x`:
   `fun r x => (n > 0 ∧ x = 1) ∨ (¬n > 0 ∧ x = 2)`. It proves
   `?pf₁ := Or.inl ⟨h₁, rfl⟩` and `?pf₂ := Or.inr ⟨h₂, rfl⟩`. Jumps under a common local share its
   binder: the jumps of an `else if` chain share the conditions above them.

The RHS goal of step 1 thus receives the hypothesis

```
(n > 0 ∧ x = 1) ∨ (¬n > 0 ∧ x = 2)
```

This `?H` is the strongest postcondition of the join body at its jumps to `__do_jp`, over the join
parameters `r` and `x`.

For a stateful program, `?H` also takes the state. Let `f` run in `StateM (Nat × Nat)` from the
state `(a, b)`, and presume that the `else` branch resets the second component to `0`. Then `?H` is

```
fun r x s => ∃ z, s = (a, z) ∧ ((n > 0 ∧ x = 1 ∧ z = b) ∨ (¬n > 0 ∧ x = 2 ∧ z = 0))
```

so `s.1 = a` follows without a case split.
-/

/-- Whether `n` names a join point: `__do_jp`, which the do-elaborator binds, or `__vcgen_jp`, which
a program or a specification binds to share a continuation. Either name can carry a decimal suffix,
as in `__vcgen_jp2`, so that one scope can bind several join points by name. -/
public def isJoinPointName (n : Name) : Bool :=
  match n.eraseMacroScopes with
  | .str .anonymous s => ["__do_jp", "__vcgen_jp"].any fun p =>
      s.startsWith p && (s.drop p.length).all Char.isDigit
  | _ => false

/-- The lattice instance of the assertions `B` of a goal `pre ⊑ rhs` with the order `instPO`. The
library orders of `Prop`, `Unit`, functions, pairs and lattices give it directly. Other orders give
the synthesized lattice whose order is `instPO`. -/
partial def latticeOfOrder? (instPO : Expr) : SymM (Option Expr) := do
  match_expr instPO with
  | CompleteLattice.toPartialOrder _ instCL => return some instCL
  | Std.Internal.Order.instPartialOrderProp =>
    return some (← mkConstS ``Std.Internal.Order.instCompleteLatticeProp)
  | Lean.Order.instPartialOrderUnit => return some (← mkConstS ``Lean.Order.instCompleteLatticeUnit)
  | Lean.Order.instOrderPi α β inst =>
    let .lam x ty body bi := inst | return none
    let some lattice ← latticeOfOrder? body | return none
    let pi ← mkConstS ``Lean.Order.instCompleteLatticePi instPO.getAppFn.constLevels!
    return some (← mkAppNS pi #[α, β, ← mkLambdaS x bi ty lattice])
  | Lean.Order.instPartialOrderProd α β instα instβ =>
    let some latticeα ← latticeOfOrder? instα | return none
    let some latticeβ ← latticeOfOrder? instβ | return none
    let prod ← mkConstS ``Lean.Order.instCompleteLatticeProd instPO.getAppFn.constLevels!
    return some (← mkAppNS prod #[α, β, latticeα, latticeβ])
  | _ =>
    if instPO.hasLooseBVars then return none
    let orderTy ← Sym.inferType instPO
    let_expr PartialOrder B := orderTy | return none
    let us := orderTy.getAppFn.constLevels!
    let some instCL ← Sym.synthInstance? (← mkAppS (← mkConstS ``CompleteLattice us) B)
      | return none
    let instCL ← shareCommon instCL
    let order ← mkAppNS (← mkConstS ``CompleteLattice.toPartialOrder us) #[B, instCL]
    unless ← Sym.isDefEqI order instPO do return none
    return some instCL

/-- Register the join point `jp := val` that the goal `goal : pre ⊑ wp⟦…⟧ post eposts ss` binds, so
that the jumps below `goal` share one proof of `val`. Returns the new scope and the goals for the
program of `goal` and for `val`, or `none` if `jp` is no join point under `+jp` or the goal's order has no lattice. -/
public def registerJoinPoint (scope : Scope) (goal : MVarId) (jp : FVarId) (val : Expr)
    (info : WPApp) : VCGenM (Option (Scope × List MVarId)) := goal.withContext do
  unless (← read).useJP && isJoinPointName (← jp.getUserName) && val.isLambda do
    return none
  let goalTy ← goal.getType
  let_expr PartialOrder.rel α inst _ _ := goalTy | return none
  let jpFVar ← mkFVarS jp
  let jpTy ← Sym.inferType jpFVar
  let numParams ← Lean.Elab.Tactic.Do.getNumJoinParams jpTy info.Prog
  let lctx ← getLCtx
  let localInsts ← getLocalInstances
  let some (hyp, top, specTy, rhsTy) ← forallBoundedTelescope jpTy numParams fun xs _ => do
      forallBoundedTelescope info.Pred info.excessArgs.size fun ss B => do
    let xs ← xs.mapM (share ·)
    let ss ← ss.mapM (share ·)
    let B ← share B
    let some instB ← latticeOfOrder? inst | return none
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
      (jp, jumps.push { proof := pf.mvarId!, args, scope }) }
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

The common part of the arguments `t₁ … tₙ` of a parameter is their anti-unifier: the most specific
term `g` with holes `z₁ … zₘ` such that each `tₖ` is `g` with the values of the holes at jump `k`.
Subterms that are one pointer stay, applications of one function are anti-unified argument by
argument, and all other subterms become holes. A parameter without a common part, as `x` above,
gets its values in the leaves.

A `let` local of a branch stands for its value. After `match o with | 0 => x := s + 1 | _ => x := s
+ 2`, the jumps pass the locals `x₁ := s + 1` and `x₂ := s + 2`, whose anti-unifier is `s + z`
with the values `1` and `2`. If the values have no common part, as `s + 1` and `s * 2`, the hole
takes the locals as its values, so the leaves are `let x₁ := s + 1; z = x₁` and
`let x₂ := s * 2; z = x₂`.
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

/-- The index of the first local after `__do_jp_spec`, and the local context of each jump. -/
structure AUContext where
  cutoff : Nat
  lctxs : Array LocalContext

abbrev AUM := ReaderT AUContext (StateRefT AUState VCGenM)

/-- `e` mentions only locals with an index below `cutoff`, the locals common to all jumps. -/
def isCommon (e : Expr) : AUM Bool := do
  let some fvarId ← getMaxFVar? e | return true
  let some d := (← getLCtx).find? fvarId | return false
  return d.index < (← read).cutoff

/-- The positions of `fn` applied to `n` arguments at which the anti-unifier has no hole: the
instances, the proofs, and the arguments that a later argument or the result type depends on. -/
def rigidArgs (fn : Expr) (n : Nat) : MetaM (Array Bool) := do
  let info ← getFunInfoNArgs fn n
  let mut rigid := info.paramInfo.map fun p => p.hasFwdDeps || p.isInstImplicit || p.isProp
  for i in info.resultDeps do
    rigid := rigid.setIfInBounds i true
  return rigid

/-- A hole with the values `ts` at the jumps. Returns `none` if its type mentions a local of a
branch. -/
def mkHole (ts : Array Expr) : AUM (Option Expr) := do
  let type ← Sym.inferType ts[0]!
  unless ← isCommon type do return none
  let fvarId ← mkFreshFVarId
  modify fun s => { s with holes := s.holes.push { fvarId, type, vals := ts } }
  return some (← mkFVarS fvarId)

/-- The value `v` of `t`, if `t` is a `let` local of a branch in `lctx` other than a `have`.
If `v` is again such a local, the value of `v`, and so on. -/
partial def lookThrough (cutoff : Nat) (lctx : LocalContext) (t : Expr) : Option Expr := do
  let .fvar fvarId := t | none
  let .ldecl index _ _ _ v nonDep _ ← lctx.find? fvarId | none
  if nonDep || index < cutoff then none
  some ((lookThrough cutoff lctx v).getD v)

mutual

/-- The anti-unifier of the subterms `ts` at one position of the jump arguments, or a hole with
the values `ts` if `ts` have no common part. Returns `none` if that hole has a type that mentions
a local of a branch. -/
partial def antiUnify (ts : Array Expr) : AUM (Option Expr) := do
  let key := ts.map ({ expr := · })
  if let some r := (← get).cache[key]? then return r
  let r ← match ← commonPart ts with
    | some g => pure (some g)
    | none => mkHole ts
  modify fun s => { s with cache := s.cache.insert key r }
  return r

/-- The common part of the subterms `ts`, `none` if they have none. Subterms that are one pointer
stay, unless they mention a local of a branch. A `let` local of a branch at jump `k` stands for
its value in the local context of jump `k`. Applications of one function to the same number of
arguments are anti-unified argument by argument, if they differ only at positions that are not
rigid. -/
partial def commonPart (ts : Array Expr) : AUM (Option Expr) := do
  let t := ts[0]!
  if ts.all (isSameExpr t ·) && (← isCommon t) then return some t
  let ctx ← read
  let vs := ts.mapIdx fun k t => (lookThrough ctx.cutoff ctx.lctxs[k]! t).getD t
  unless (vs.zip ts).all fun (v, t) => isSameExpr v t do
    return ← commonPart vs
  let fn := t.getAppFn
  let n := t.getAppNumArgs
  unless n > 0 && ts.all (fun s => isSameExpr s.getAppFn fn && s.getAppNumArgs == n) do
    return none
  unless ← isCommon fn do return none
  let saved ← get
  let rigid ← rigidArgs fn n
  let argss := ts.map (·.getAppArgs)
  let mut args := Array.mkEmpty n
  for i in [:n] do
    let ai := argss.map (·[i]!)
    let a := ai[0]!
    if ai.all (isSameExpr a ·) && (← isCommon a) then
      args := args.push a
    else if rigid[i]?.getD true then
      set saved
      return none
    else if let some a ← antiUnify ai then
      args := args.push a
    else
      set saved
      return none
  return some (← mkAppNS fn args)

end

/-- A column of the leaves: the equation `lhs = vals[k]` at type `type` in the leaf of jump `k`. -/
structure Column where
  lhs : Expr
  type : Expr
  vals : Array Expr

/-- The anti-unifier of the arguments of `jumps` for the parameters `xs` of `?H`. Returns the pairs
`(j, g)` of the parameters `xs[j]` with a common part `g`, the columns of the leaves, and the holes.
A parameter without a common part has a column of its own. The parameters of type `PUnit`, such as
the result `__r` of a `Unit` statement, get no equation. -/
def antiUnifyJumps (jp : JoinPoint) (xs : Array Expr) (jumps : Array Jump) :
    VCGenM (Array (Nat × Expr) × Array Column × Array Hole) := do
  let some jump₀ := jumps[0]? | return (#[], #[], #[])
  let types ← xs.mapM (Sym.inferType ·)
  let decl₀ ← jump₀.proof.getDecl
  let cutoff := (decl₀.lctx.get! jp.spec.fvarId!).index + 1
  let ctx : AUContext := { cutoff, lctxs := ← jumps.mapM fun jump => return (← jump.proof.getDecl).lctx }
  let go : AUM (Array (Nat × Expr) × Array Column) := do
    -- A position whose subterms are the arguments of a parameter becomes that parameter.
    for h : j in [:xs.size] do
      unless types[j]!.isConstOf ``PUnit do
        let x ← share xs[j]
        let key := jumps.map ({ expr := ·.args[j]! })
        modify fun s => { s with cache := s.cache.insert key (some x) }
    let mut eqs := #[]
    let mut columns := #[]
    for h : j in [:xs.size] do
      if types[j]!.isConstOf ``PUnit then continue
      let ts := jumps.map (·.args[j]!)
      if let some g ← commonPart ts then
        eqs := eqs.push (j, g)
      else
        columns := columns.push { lhs := xs[j], type := types[j]!, vals := ts }
    return (eqs, columns)
  let ((eqs, columns), st) ← withLCtx decl₀.lctx decl₀.localInstances ((go.run ctx).run {})
  let holeColumns := st.holes.map fun h => { lhs := mkFVar h.fvarId, type := h.type, vals := h.vals }
  return (eqs, columns ++ holeColumns, st.holes)

/-- The proof of the conjunction `φ = mkAndN ps` from the proofs `pfs` of its conjuncts `ps`. -/
partial def mkConjProof (φ : Expr) : List Expr → MetaM Expr
  | [] => return mkConst ``True.intro
  | [pf] => return pf
  | pf :: pfs => do
    let_expr And a b := φ | throwError "vcgen +jp: expected `∧`{indentExpr φ}"
    return mkApp4 (mkConst ``And.intro) a b pf (← mkConjProof b pfs)

/-- A binder of `?H` at a jump: an `∃` or a conjunct with its witness or proof, a conjunction with
the proofs of its conjuncts, or a `let`. -/
inductive Step where
  | bind (e : Expr)
  | conj (pfs : List Expr)
  | letLocal

/-- A proof of `φ` by the `step` at its head, with `k` proving the rest of `φ`. -/
def mkStepProof (φ : Expr) (step : Step) (k : Expr → MetaM Expr) : MetaM Expr := do
  match step with
  | .letLocal =>
    -- `bindLocal` drops a `let` that the rest of `φ` does not use.
    let .letE _ _ v b _ := φ | k φ
    k (b.instantiate1 v)
  | .conj pfs =>
    let_expr And a b := φ | throwError "vcgen +jp: expected `∧`{indentExpr φ}"
    return mkApp4 (mkConst ``And.intro) a b (← mkConjProof a pfs) (← k b)
  | .bind e =>
    match_expr φ with
    | Exists α p =>
      return mkApp4 (mkConst ``Exists.intro φ.getAppFn.constLevels!) α p e (← k (p.beta #[e]))
    | And a b => return mkApp4 (mkConst ``And.intro) a b e (← k b)
    | _ => throwError "vcgen +jp: unexpected binder{indentExpr φ}"

/-- A proof of `φ` by `steps`, with `k` proving the rest of `φ`. -/
def mkStepsProof (φ : Expr) (steps : List Step) (k : Expr → MetaM Expr) : MetaM Expr :=
  match steps with
  | [] => k φ
  | step :: steps => mkStepProof φ step fun φ => mkStepsProof φ steps k

/-- A proof of `φ`, a trie of `mkTrie` at the arguments of a jump, along the `path` of the jump,
with one of the `steps` of its locals below each disjunct, and the conjuncts `leafPfs` in its
leaf. -/
partial def mkTrieProof (φ : Expr) (path : List (Nat × Nat)) (steps : List Step)
    (leafPfs : List Expr) : MetaM Expr := do
  let (g, n) :: path := path | throwError "vcgen +jp: empty path into{indentExpr φ}"
  mkOrIntro φ g 0 n fun φ => do
    if path.isEmpty then
      return ← mkConjProof φ leafPfs
    let step :: steps := steps | throwError "vcgen +jp: missing local for{indentExpr φ}"
    mkStepProof φ step fun φ => mkTrieProof φ path steps leafPfs

/-- The `vcgen` simp normal form `e'` of `e` under `scope` with a proof of `e = e'`, or `e` with
`none` if `vcgen` has no simp methods or simp makes no progress. -/
def simpJoinTerm (scope : Scope) (e : Expr) : VCGenM (Expr × Option Expr) := do
  let e ← shareCommonInc e
  match ← runSimp scope Sym.Simp.simp e with
  | .rfl .. => return (e, none)
  | .step e' proof .. => return (e', some proof)

/-- The equation `lhs = rhs` at type `α`, with `rhs` in `simp` normal form `rhs'` under `scope`, and
the proof of `rhs = rhs'` if `simp` makes progress. -/
def mkJoinEq (scope : Scope) (α lhs rhs : Expr) : VCGenM (Expr × Option Expr) := do
  let (rhs', pf?) ← simpJoinTerm scope rhs
  return (mkApp3 (mkConst ``Eq [← Sym.getLevel α]) α lhs rhs', pf?)

/-- The proof `pf? : rhs = rhs'` of an equation `lhs = rhs'` of `mkJoinEq` at a jump that passes
`lhs = rhs`, or `rfl : lhs = lhs` if `simp` made no progress. -/
def mkJoinEqProof (lhs : Expr) (pf? : Option Expr) : VCGenM Expr := do
  if let some pf := pf? then return pf
  let α ← Sym.inferType lhs
  return mkApp2 (mkConst ``Eq.refl [← Sym.getLevel α]) α lhs

/-- If `goal` is the RHS goal `∀ xs, ?H xs → …` of a pending join point `jp`, assign `?H` the
anti-unifier of the arguments of the jumps to `jp` above the trie of the jumps, `False` if no jump
reaches `jp`, and each jump's `?pf` its proof, and return `goal` with its binders introduced.
Otherwise return `goal`. The values in the leaves are in `simp` normal form, so the RHS goal
introduces `?H xs` without `simp`. `vcgen` processes the RHS goal after all goals below the
registration, so every jump is known by then. -/
public def finalizeJoinPoint (goal : MVarId) : VCGenM MVarId := do
  let some (jp, jumps) := (← get).pendingJoinPoints[goal]? | return goal
  modify fun st => { st with pendingJoinPoints := st.pendingJoinPoints.erase goal }
  let jumpsLocals ← jumps.mapM fun jump => return (jump, ← jumpLocals jp jump)
  let (paths, holes, eqParams, leafPfs) ← jp.hyp.withContext do
      forallTelescope (← jp.hyp.getType) fun xs _ => do
    let (eqs, columns, holes) ← antiUnifyJumps jp xs jumps
    -- The leaf of each jump `k`, with the proofs of `vals[k] = vals[k]'` in the context of `k`.
    let leaves ← (Array.range jumps.size).mapM fun k => do
      let decl ← jumps[k]!.proof.getDecl
      withLCtx decl.lctx decl.localInstances do
        columns.mapM fun c =>
          return (c.vals[k]!, ← mkJoinEq jumps[k]!.scope c.type c.lhs c.vals[k]!)
    let trieJumps := (jumpsLocals.zip leaves).map fun ((jump, locals), leaf) =>
      (jump, locals, mkAndN (leaf.map (·.2.1)).toList)
    let (trie, paths) ← mkTrie trieJumps 0
    let eqTerms ← eqs.mapM fun (j, g) => do
      let α ← Sym.inferType xs[j]!
      return mkApp3 (mkConst ``Eq [← Sym.getLevel α]) α xs[j]! g
    let body := if eqs.isEmpty then trie else mkAnd (mkAndN eqTerms.toList) trie
    let lctx := holes.foldl (init := ← getLCtx) fun lctx h => lctx.mkLocalDecl h.fvarId `z h.type
    let φ ← withLCtx lctx (← getLocalInstances) do
      holes.foldrM (init := body) fun h φ => do
        return mkApp2 (mkConst ``Exists [← Sym.getLevel h.type]) h.type
          (← mkLambdaFVars #[mkFVar h.fvarId] φ)
    jp.hyp.assign (← mkLambdaFVars xs φ)
    return (paths, holes, eqs.map (·.1), leaves.map (·.map fun (v, _, pf?) => (v, pf?)))
  for h : k in [:jumpsLocals.size] do
    let (jump, locals) := jumpsLocals[k]
    jump.proof.withContext do
      let φ ← instantiateMVars (← jump.proof.getType)
      let eqPfsₖ ← eqParams.mapM fun j => mkJoinEqProof jump.args[j]! none
      let leafPfsₖ ← leafPfs[k]!.mapM fun (v, pf?) => mkJoinEqProof v pf?
      -- The values of the holes at jump `k` witness the `∃`s above the equations and the trie.
      let top := holes.toList.map (Step.bind ·.vals[k]!) ++
        if eqParams.isEmpty then [] else [Step.conj eqPfsₖ.toList]
      let steps := locals.toList.map fun d => if d.value?.isSome then .letLocal else .bind d.toExpr
      jump.proof.assign
        (← mkStepsProof φ top fun φ => mkTrieProof φ paths[k]! steps leafPfsₖ.toList)
  introsHygienic goal

end Lean.Elab.Tactic.VCGen
