/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Reser
-/
module

prelude
public import Lean.Meta.Basic
public import Lean.Meta.HasAssignableMVar
public import Lean.Meta.InferType
public import Lean.Meta.ExprDefEq
public import Lean.Meta.GetUnfoldableConst
public import Lean.Meta.FunInfo
public import Lean.Meta.AppBuilder
public import Lean.Meta.Tactic.Simp.SimpTheorems
import Lean.Meta.WHNF
public import Lean.Meta.Match.MatcherApp.Basic

public section

/-!
# Runtime Representation and Matching for Quasi-Quoted `Expr` Patterns

Defines:
- `ExprMatchEngine`, `ExprMatchItem`, `ExprMatchFlags`, `ExprMatchRel`, and `ResolvedExprMatchRel`
  for configuring structural and definitional matching relations (`structural`, `reducible`,
  `instances`, `defeq`, `sym`, `[±item, ...]`, and `±inst`/`±beta`/`±zeta`/`±proj`/`±eta`).
- `ExprPattern` and `ExprPattern.compile`, supporting:
  - `O(|pattern|)` structural matching with wildcard elision, lazy head-mvar resolution, empty-bound
    and closed-subterm `hasAnyFVar` skips,
  - syntactic/pointer-equality fast path before proof-irrelevance checks on closed mismatches,
  - precomputed pattern `levelParam` node sets and `.const`/`.sort` universe level checks,
  - direct pin pre-seeding and per-site `ResolvedExprMatchRel` runtime caching, and
  - lazy look-through with consistent `let`-rewrapping across structural and `isDefEq` engines.
- `ExprContext` (`ExprContext.fill`), `localHypTypes`, `localHypDecls`, `Subterms` (`subterms`),
  and `MatchDiscriminants` (`matchDiscriminants`).
-/

namespace Lean.Meta

/--
Engine selecting how an `ExprPattern` is matched against a target `Expr`.

Note on `let` preservation: `/structural +zeta` is the faithful non-substituting look-through
engine. The `isDefEq`-based engines (`/reducible`, `/instances`, `/defeq`) lift and re-wrap outer
or inspected `let` expressions when possible, but still fall back to `isDefEq` substitution when a
`let` value depends on a pattern binder, and may return captures in `isDefEq`-normalized form.
-/
inductive ExprMatchEngine where
  /-- Truly syntactic structural matching (modulo `mdata`, assigned metavariables, and proofs). -/
  | structural
  /--
  Definitional equality with `.reducible` transparency as the base unfold set (see `ExprMatchEngine`
  notes on `isDefEq` `let`-substitution and normalization).
  -/
  | reducible
  /--
  Definitional equality with `.instances` transparency as the base unfold set (see `ExprMatchEngine`
  notes on `isDefEq` `let`-substitution and normalization).
  -/
  | instances
  /--
  Definitional equality with `.default` transparency as the base unfold set (see `ExprMatchEngine`
  notes on `isDefEq` `let`-substitution and normalization).
  -/
  | defeq
  /-- Sym matching engine (runtime implemented in B5). -/
  | sym
  deriving Inhabited, BEq, Repr

/-- A static constant or simp-set item in an expr quotation relation `[items]` list. -/
structure ExprMatchItem where
  /-- `true` to allow unfolding, `false` to block unfolding. -/
  positive  : Bool
  /-- Constant or simp-set name. -/
  declName  : Name
  /-- `true` if `declName` names a registered simp set (e.g. `simp` or `my_simps`). -/
  isSimpSet : Bool := false
  deriving Inhabited, BEq, Repr

/-- Overrides for `±inst`, `±beta`, `±zeta`, `±proj`, `±eta` in an expr quotation relation. -/
structure ExprMatchFlags where
  /-- Override for instance-implicit argument definitional matching (`±inst`). -/
  inst : Option Bool := none
  /-- Override for beta-reduction (`±beta`). -/
  beta : Option Bool := none
  /-- Override for `let` and context `zetaDelta` look-through (`±zeta`). -/
  zeta : Option Bool := none
  /-- Override for structure projection reduction (`±proj`). -/
  proj : Option Bool := none
  /-- Override for eta equivalence/expansion (`±eta`). -/
  eta  : Option Bool := none
  deriving Inhabited, BEq, Repr

/-- Resolved matching flags after applying engine defaults (no `Option`). -/
structure ResolvedExprMatchFlags where
  /-- Compare instance-implicit arguments via `.instances` `isDefEq` when structural fails. -/
  inst : Bool
  /-- Allow beta-reduction during matching. -/
  beta : Bool
  /-- Allow `let`-expression and local-def `zetaDelta` unfolding/look-through. -/
  zeta : Bool
  /-- Allow structure projection reduction. -/
  proj : Bool
  /-- Allow eta equivalence/expansion. -/
  eta  : Bool
  deriving Inhabited, BEq, Repr

/-- Matching relation specification for an `` `(expr[rel]| ...) `` quotation. -/
structure ExprMatchRel where
  /-- Base matching engine. -/
  engine : ExprMatchEngine := .structural
  /-- Static constant and simp-set unfold overrides, evaluated left-to-right. -/
  items  : Array ExprMatchItem := #[]
  /-- Explicit `±flag` overrides relative to the engine defaults. -/
  flags  : ExprMatchFlags := {}
  deriving Inhabited, BEq, Repr

/-- Resolve engine defaults with explicit flag overrides. -/
def ExprMatchRel.resolveFlags (rel : ExprMatchRel) : ResolvedExprMatchFlags :=
  let d := match rel.engine with
    | .structural => false
    | .reducible | .instances | .defeq | .sym => true
  { inst := rel.flags.inst.getD d
    beta := rel.flags.beta.getD d
    zeta := rel.flags.zeta.getD d
    proj := rel.flags.proj.getD d
    eta  := rel.flags.eta.getD d }

/--
A pre-validated, pre-resolved matching relation produced by `ExprMatchRel.resolveStatic` and
`ResolvedExprMatchRel.withLocalItems`. Caching this across repeated match attempts avoids repeating
simp-extension lookups and declaration validation per scrutinee.
-/
structure ResolvedExprMatchRel where
  /-- Base matching engine. -/
  engine        : ExprMatchEngine
  /-- Resolved boolean flags. -/
  flags         : ResolvedExprMatchFlags
  /-- Validated static unfold rules in reverse order (later rules override earlier ones). -/
  itemRulesRev  : Array (Bool × Sum Name SimpTheorems) := #[]
  /-- Validated positive local `let` free variables (`+$x`). -/
  posFVars      : Array FVarId := #[]
  /-- Validated negative local `let` free variables (`-$x`). -/
  negFVars      : Array FVarId := #[]
  /-- `true` if any unfolding feature or item override is active. -/
  hasUnfolding  : Bool := false
  deriving Inhabited

private def simpTheoremsUnfolds (thms : SimpTheorems) (declName : Name) : Bool :=
  thms.isDeclToUnfold declName ||
    (thms.toUnfoldThms.contains declName && !thms.erased.contains (.decl declName))

private def emptyResolvedRel (rel : ExprMatchRel) : ResolvedExprMatchRel :=
  let flags := rel.resolveFlags
  { engine := rel.engine
    flags
    hasUnfolding := flags.beta || flags.zeta || flags.proj || flags.eta }

private structure CachedSiteRel where
  rel         : ExprMatchRel
  constGen    : Nat
  declLogSize : Nat
  isExporting : Bool
  mainModule  : Name
  resolved    : ResolvedExprMatchRel
  simpSlots   : Array (Nat × SimpExtension × Bool)

private builtin_initialize resolvedRelCacheRef : IO.Ref (Std.HashMap Name CachedSiteRel) ←
  IO.mkRef {}

private def resolveStaticCore (rel : ExprMatchRel) :
    MetaM (ResolvedExprMatchRel × Array (Nat × SimpExtension × Bool)) := do
  if rel.items.isEmpty then
    return (emptyResolvedRel rel, #[])
  let env ← getEnv
  let flags := rel.resolveFlags
  let mut rulesRev : Array (Bool × Sum Name SimpTheorems) := #[]
  let mut simpSlotsFwd : Array (Nat × SimpExtension × Bool) := #[]
  let mut posConsts : NameHashSet := {}
  let mut posSimpSets : Array SimpTheorems := #[]
  for item in rel.items do
    if item.isSimpSet then
      let some ext ← getSimpExtension? item.declName
        | throwError "unknown simp attribute `{item.declName}`"
      let thms ← ext.getTheorems
      if !item.positive && rel.engine == .structural then
        if posSimpSets.isEmpty && posConsts.isEmpty then
          throwError "invalid relation item `-{item.declName}`: \
            `structural` does not unfold any simp-set definitions by default"
      if item.positive then
        posSimpSets := posSimpSets.push thms
      simpSlotsFwd := simpSlotsFwd.push (rulesRev.size, ext, item.positive)
      rulesRev := rulesRev.push (item.positive, .inr thms)
    else
      unless env.contains item.declName do
        throwError "unknown constant `{item.declName}` in expr match relation"
      if !item.positive && rel.engine == .structural then
        let inPosSimp := posSimpSets.any (simpTheoremsUnfolds · item.declName)
        unless posConsts.contains item.declName || inPosSimp do
          throwError "invalid relation item `-{item.declName}`: \
            `structural` does not unfold `{item.declName}` by default"
      if item.positive then
        posConsts := posConsts.insert item.declName
      rulesRev := rulesRev.push (item.positive, .inl item.declName)
  let n := rulesRev.size
  rulesRev := rulesRev.reverse
  let simpSlots := simpSlotsFwd.map fun (fwdIdx, ext, pos) => (n - 1 - fwdIdx, ext, pos)
  let resolved : ResolvedExprMatchRel := {
    engine       := rel.engine
    flags
    itemRulesRev := rulesRev
    hasUnfolding := flags.beta || flags.zeta || flags.proj || flags.eta || !rulesRev.isEmpty
  }
  return (resolved, simpSlots)

/--
Validate static `[items]` rules and resolve simp attributes once per site.
Rejects unknown constants, unknown simp attributes, and `-item` overrides over an empty
`structural` base.
-/
def ExprMatchRel.resolveStatic (rel : ExprMatchRel) : MetaM ResolvedExprMatchRel := do
  return (← resolveStaticCore rel).1

/--
Cached variant of `ExprMatchRel.resolveStatic` keyed by `siteId` in a runtime `IO.Ref`.
Validates against `Environment` counters (`constGen`, `declChangeLog.size`, `isExporting`,
`mainModule`) without `ObjectPtr` or `modifyEnv`, and refreshes simp extension states in `O(1)`
without re-calling `getSimpExtension?` or re-validating constants.
-/
def ExprMatchRel.resolveStaticCached (siteId : Name) (rel : ExprMatchRel) :
    MetaM ResolvedExprMatchRel := do
  if rel.items.isEmpty then
    return emptyResolvedRel rel
  if siteId.isAnonymous then
    return ← rel.resolveStatic
  let env ← getEnv
  if let some entry := (← resolvedRelCacheRef.get)[siteId]? then
    if entry.rel == rel && entry.constGen == env.constGen &&
        entry.declLogSize == env.declChangeLog.size &&
        entry.isExporting == env.isExporting &&
        entry.mainModule == env.header.mainModule then
      if entry.simpSlots.isEmpty then
        return entry.resolved
      let mut rulesRev := entry.resolved.itemRulesRev
      for (revIdx, ext, pos) in entry.simpSlots do
        rulesRev := rulesRev.setIfInBounds revIdx (pos, .inr (ext.getState env))
      return { entry.resolved with itemRulesRev := rulesRev }
  let (resolved, simpSlots) ← resolveStaticCore rel
  let cached : CachedSiteRel := {
    rel
    constGen    := env.constGen
    declLogSize := env.declChangeLog.size
    isExporting := env.isExporting
    mainModule  := env.header.mainModule
    resolved
    simpSlots
  }
  resolvedRelCacheRef.modify (·.insert siteId cached)
  return resolved

@[inline]
private def instantiateMVarsIfNeeded (e : Expr) : MetaM Expr :=
  if e.hasExprMVar || e.hasLevelMVar then instantiateMVars e else pure e

private def resolveHeadMVar (e : Expr) : MetaM Expr := do
  go (maxRecDepth.get (← getOptions)) e
where
  go (fuel : Nat) (cur : Expr) : MetaM Expr := do
    let cur := cur.consumeMData
    if !cur.hasExprMVar then
      return cur
    let fn := cur.getAppFn.consumeMData
    if !fn.isMVar then
      return cur
    match fuel with
    | 0 => throwError maxRecDepthErrorMessage
    | fuel + 1 =>
      let fn' ← instantiateMVars fn
      if fn' == fn then
        return cur
      let res := (mkAppN fn' cur.getAppArgs).consumeMData
      if res.getAppFn.consumeMData.isMVar then go fuel res else pure res

/--
Validate and attach local `$x` definition overrides `(positive, expr)` onto a statically resolved
relation `r`. Each item must denote a free variable referring to a dependent `let` declaration in
the current local context; `-$x` fails if neither `+zeta` nor a prior `+$x` enables unfolding `x`.
-/
def ResolvedExprMatchRel.withLocalItems (r : ResolvedExprMatchRel)
    (localItems : Array (Bool × Expr)) : MetaM ResolvedExprMatchRel := do
  if localItems.isEmpty then
    let hasUnf := r.flags.beta || r.flags.zeta || r.flags.proj || r.flags.eta ||
      !r.itemRulesRev.isEmpty
    return { r with posFVars := #[], negFVars := #[], hasUnfolding := hasUnf }
  let lctx ← getLCtx
  let mut pos : Array FVarId := #[]
  let mut neg : Array FVarId := #[]
  for (isPos, rawE) in localItems do
    let e ← instantiateMVarsIfNeeded rawE
    let .fvar fv := e.consumeMData
      | throwError "local relation item `$...` must evaluate to a free variable, \
          got{indentExpr e}"
    let some decl := lctx.find? fv
      | throwError "local relation item `{e}` is not in the local context"
    if (decl.value? (allowNondep := false)).isNone then
      throwError "local relation item `{mkFVar fv}` is not a `let`-bound local definition \
        (non-dependent `have` and non-let hypotheses cannot be unfolded)"
    if isPos then
      pos := pos.filter (· != fv)
      neg := neg.filter (· != fv)
      pos := pos.push fv
    else
      unless r.flags.zeta || pos.contains fv do
        throwError "invalid local relation item `-{mkFVar fv}`: \
          local definitions are not unfolded by default under this relation"
      pos := pos.filter (· != fv)
      neg := neg.filter (· != fv)
      neg := neg.push fv
  return {
    r with
    posFVars     := pos
    negFVars     := neg
    hasUnfolding := r.flags.beta || r.flags.zeta || r.flags.proj || r.flags.eta ||
      !r.itemRulesRev.isEmpty || !pos.isEmpty || !neg.isEmpty
  }

/-- Resolve both static `[items]` and dynamic local `$x` items in one call. -/
def ExprMatchRel.resolve (rel : ExprMatchRel)
    (localItems : Array (Bool × Expr) := #[]) (siteId : Name := .anonymous) :
    MetaM ResolvedExprMatchRel := do
  let r ←
    if rel.items.isEmpty then
      pure (emptyResolvedRel rel)
    else
      rel.resolveStaticCached siteId
  if localItems.isEmpty then
    return r
  r.withLocalItems localItems

private def levelHasPatParam (patParams : List Name) : Level → Bool
  | .zero      => false
  | .succ u    => levelHasPatParam patParams u
  | .max u v   => levelHasPatParam patParams u || levelHasPatParam patParams v
  | .imax u v  => levelHasPatParam patParams u || levelHasPatParam patParams v
  | .param n   => patParams.contains n
  | .mvar _    => false

private def hasPatLevelParam (patParams : List Name) (e : Expr) : Bool :=
  if patParams.isEmpty || !e.hasLevelParam then false else go e
where
  go (e : Expr) : Bool :=
    if !e.hasLevelParam then false
    else match e with
      | .sort u           => levelHasPatParam patParams u
      | .const _ us       => us.any (levelHasPatParam patParams)
      | .app f a          => go f || go a
      | .lam _ t b _      => go t || go b
      | .forallE _ t b _  => go t || go b
      | .letE _ t v b _   => go t || go v || go b
      | .mdata _ b        => go b
      | .proj _ _ b       => go b
      | _                 => false

private def computePatLevelNodes (patParams : List Name) (body : Expr) : ExprSet :=
  if patParams.isEmpty || !body.hasLevelParam then {}
  else
    let (_, st) := (go body).run (({} : ExprMap Bool), ({} : ExprSet))
    st.2
where
  go : Expr → StateM (ExprMap Bool × ExprSet) Bool
    | .mdata _ b => go b
    | e => do
      if !e.hasLevelParam then
        return false
      if let some cached := (← get).1[e]? then
        return cached
      let res ← match e with
        | .sort u          => pure (levelHasPatParam patParams u)
        | .const _ us      => pure (us.any (levelHasPatParam patParams))
        | .app f a         =>
          let hf ← go f
          let ha ← go a
          pure (hf || ha)
        | .lam _ t b _     =>
          let ht ← go t
          let hb ← go b
          pure (ht || hb)
        | .forallE _ t b _ =>
          let ht ← go t
          let hb ← go b
          pure (ht || hb)
        | .letE _ t v b _  =>
          let ht ← go t
          let hv ← go v
          let hb ← go b
          pure (ht || hv || hb)
        | .proj _ _ b      => go b
        | _                => pure false
      modify fun (memo, set) =>
        (memo.insert e res, if res then set.insert e else set)
      return res

private def stripOuterLambdas : Nat → Expr → Expr
  | n + 1, .lam _ _ b _ => stripOuterLambdas n b
  | _,     e            => e

/--
A compiled `Expr` pattern `lam = fun x₀ … xₙ₋₁ => body`, closed up to `levelParams`.
Wildcards, unresolved implicits, pins (`$e`), and `?`-binders are all abstracted as lambdas;
`namedIdx` locates the `?`-binders in source order.
-/
structure ExprPattern where
  /-- Universe parameter names abstracted in `lam`. -/
  levelParams   : List Name
  /-- Pattern expression wrapped in `numVars` outer lambdas. -/
  lam           : Expr
  /-- Number of outer lambda binders in `lam`. -/
  numVars       : Nat
  /-- Index (into `x₀ … xₙ₋₁`) of each named `?`-binder, in order of first occurrence. -/
  namedIdx      : Array Nat
  /-- `true` for variables that should only be solved first-order in structural matching. -/
  firstOrder    : Array Bool
  /--
  `true` if variable `i` may need materializing (it is named or occurs multiple times).
  If empty on an uncompiled pattern, every variable is treated as potentially captured.
  -/
  captureVars   : Array Bool := #[]
  /-- Map from closed proof subterms of `body` (modulo `mdata`) to their inferred types. -/
  closedProofs  : ExprMap Expr := {}
  /-- Subterms of `body` (modulo `mdata`) mentioning a pattern parameter in `levelParams`. -/
  patLevelNodes : ExprSet := {}
  /-- `true` if `compile` populated `captureVars` and `closedProofs`. -/
  precomputed   : Bool := false
  deriving Inhabited

/-- Construct a precompiled `ExprPattern` from serialized fields (used by elaborated patterns). -/
def ExprPattern.mkCompiled (levelParams : List Name) (lam : Expr) (numVars : Nat)
    (namedIdx : Array Nat) (firstOrder captureVars : Array Bool)
    (closedProofsList : List (Expr × Expr)) (precomputed : Bool) : ExprPattern :=
  let body := stripOuterLambdas numVars lam
  { levelParams, lam, numVars, namedIdx, firstOrder, captureVars
    closedProofs := closedProofsList.foldl (init := {}) fun m (k, v) => m.insert k v
    patLevelNodes := computePatLevelNodes levelParams body
    precomputed }

/-- Return the body of `p` with the `p.numVars` outer lambdas stripped. -/
def ExprPattern.body (p : ExprPattern) : Expr :=
  stripOuterLambdas p.numVars p.lam

/-- Project the values of the named `?`-binders from the full variable assignment `σ`. -/
def ExprPattern.named [Inhabited α] (p : ExprPattern) (σ : Array α) : Array α :=
  p.namedIdx.map (σ.getD · default)

@[inline]
private def ExprPattern.shouldCapture (p : ExprPattern) (k : Nat) : Bool :=
  p.captureVars.getD k true

@[inline]
private def hasPatLevelFast (pat : ExprPattern) (isOrigPat : Bool) (e : Expr) : Bool :=
  if pat.levelParams.isEmpty || !e.hasLevelParam then
    false
  else if isOrigPat && pat.precomputed then
    pat.patLevelNodes.contains e
  else
    hasPatLevelParam pat.levelParams e

private def computeCaptureVars (body : Expr) (numVars : Nat) (namedIdx : Array Nat) :
    Array Bool := Id.run do
  let mut occs : Array Nat := .replicate numVars 0
  let rec count (e : Expr) (depth : Nat) (occs : Array Nat) : Array Nat :=
    if e.looseBVarRange <= depth then
      occs
    else match e with
      | .bvar i =>
        if i >= depth && i - depth < numVars then
          let k := numVars - 1 - (i - depth)
          let c := occs.getD k 0
          if c >= 2 then occs else occs.setIfInBounds k (c + 1)
        else
          occs
      | .app f a         => count a depth (count f depth occs)
      | .lam _ t b _     => count b (depth + 1) (count t depth occs)
      | .forallE _ t b _ => count b (depth + 1) (count t depth occs)
      | .letE _ t v b _  => count b (depth + 1) (count v depth (count t depth occs))
      | .mdata _ b       => count b depth occs
      | .proj _ _ b      => count b depth occs
      | _                => occs
  occs := count body 0 occs
  let mut capture : Array Bool := .replicate numVars false
  for k in *...numVars do
    if occs.getD k 0 >= 2 then
      capture := capture.setIfInBounds k true
  for idx in namedIdx do
    capture := capture.setIfInBounds idx true
  return capture

private def collectClosedProofs (patParams : List Name) (body : Expr) :
    MetaM (ExprMap Expr) := do
  withLCtx {} {} do
    let (_, st) ← (go body).run (({}, {}) : Std.HashSet Expr × ExprMap Expr)
    return st.2
where
  canBeProof : Expr → Bool
    | .bvar _ | .sort _ | .lit _ | .forallE _ _ _ _ | .mvar _ => false
    | _ => true
  go : Expr → StateRefT (Std.HashSet Expr × ExprMap Expr) MetaM Unit
    | .mdata _ b => go b
    | e => do
      if (← get).1.contains e then
        return
      modify fun (vis, pf) => (vis.insert e, pf)
      if !e.hasLooseBVars && !e.hasFVar && !hasPatLevelParam patParams e && canBeProof e then
        try
          if ← isProof e then
            let ty ← instantiateMVarsIfNeeded (← inferType e)
            if !ty.hasMVar && !ty.hasFVar then
              modify fun (vis, pf) => (vis, pf.insert e ty)
        catch _ =>
          pure ()
      match e with
      | .app f a         => go f; go a
      | .lam _ t b _     => go t; go b
      | .forallE _ t b _ => go t; go b
      | .letE _ t v b _  => go t; go v; go b
      | .proj _ _ b      => go b
      | _                => pure ()

/--
Precompute `captureVars`, `closedProofs`, and `patLevelNodes` for `p` so structural matching skips
materializing single-occurrence wildcards, rejects non-proof closed mismatches in `O(1)`, and checks
pattern universe parameters without re-traversing subterms.
-/
def ExprPattern.compile (p : ExprPattern) : MetaM ExprPattern := do
  let body := p.body
  let captureVars := computeCaptureVars body p.numVars p.namedIdx
  let closedProofs ← collectClosedProofs p.levelParams body
  let patLevelNodes := computePatLevelNodes p.levelParams body
  return { p with captureVars, closedProofs, patLevelNodes, precomputed := true }

/--
Substitute runtime pin values `vals[j]` for the abstracted pattern variables at `idx[j]`.
Indices in `idx` must be distinct and `< p.numVars`.
-/
def ExprPattern.instantiate (p : ExprPattern) (idx : Array Nat) (vals : Array Expr) : ExprPattern :=
  if idx.isEmpty then p else
  let shift (i : Nat) := i - (idx.filter (· < i)).size
  { p with
    lam           := go p.numVars 0 p.lam
    numVars       := p.numVars - idx.size
    namedIdx      := p.namedIdx.map shift
    firstOrder    := (p.firstOrder.zipIdx.filter (!idx.contains ·.2)).map (·.1)
    captureVars   :=
      if p.captureVars.isEmpty then #[]
      else (p.captureVars.zipIdx.filter (!idx.contains ·.2)).map (·.1)
    closedProofs  := {}
    patLevelNodes := {}
    precomputed   := false }
where
  go : Nat → Nat → Expr → Expr
    | n + 1, i, .lam x t b bi =>
      match idx.idxOf? i with
      | some j => go n (i + 1) (b.instantiate1 (vals.getD j default))
      | none   => .lam x t (go n (i + 1) b) bi
    | _, _, e => e

private def eqModMData (a b : Expr) : Bool :=
  match a, b with
  | .mdata _ a', b' => eqModMData a' b'
  | a', .mdata _ b' => eqModMData a' b'
  | .app f₁ a₁, .app f₂ a₂ => eqModMData f₁ f₂ && eqModMData a₁ a₂
  | .lam _ d₁ b₁ _, .lam _ d₂ b₂ _ => eqModMData d₁ d₂ && eqModMData b₁ b₂
  | .forallE _ d₁ b₁ _, .forallE _ d₂ b₂ _ => eqModMData d₁ d₂ && eqModMData b₁ b₂
  | .letE _ t₁ v₁ b₁ _, .letE _ t₂ v₂ b₂ _ =>
    eqModMData t₁ t₂ && eqModMData v₁ v₂ && eqModMData b₁ b₂
  | .proj s₁ i₁ e₁, .proj s₂ i₂ e₂ => s₁ == s₂ && i₁ == i₂ && eqModMData e₁ e₂
  | _, _ => a == b
termination_by sizeOf a + sizeOf b

private structure LetEntry where
  fv       : FVarId
  userName : Name
  type     : Expr
  val      : Expr
  nondep   : Bool
  deriving Inhabited

private def rewrapLets (e : Expr) (lets : Array LetEntry) : Expr :=
  if lets.isEmpty || !e.hasFVar then e else
    lets.foldr (init := e) fun entry res =>
      if res.hasAnyFVar (· == entry.fv) then
        mkLet entry.userName entry.type entry.val
          (res.abstract #[mkFVar entry.fv]) entry.nondep
      else
        res

private def substAssigned (e : Expr) (σ : Array (Option Expr)) (numVars : Nat) : Expr :=
  if !e.hasLooseBVars then e else go e 0
where
  go (e : Expr) (depth : Nat) : Expr :=
    if !e.hasLooseBVars then e else
    match e with
    | .bvar i =>
      if i >= depth then
        let k := numVars - 1 - (i - depth)
        match σ.getD k none with
        | some v => v
        | none   => e
      else e
    | .app f a         => .app (go f depth) (go a depth)
    | .lam n t b bi    => .lam n (go t depth) (go b (depth + 1)) bi
    | .forallE n t b bi => .forallE n (go t depth) (go b (depth + 1)) bi
    | .letE n t v b nd => .letE n (go t depth) (go v depth) (go b (depth + 1)) nd
    | .mdata m b       => .mdata m (go b depth)
    | .proj s i b      => .proj s i (go b depth)
    | _                => e

private def substAssignedLevels (e : Expr) (patParams : List Name)
    (levels : Array (Option Level)) : Expr :=
  if patParams.isEmpty || !e.hasLevelParam || levels.all (·.isNone) then e
  else
    let lvlSubst := patParams.zip levels.toList |>.filterMap fun (n, l?) =>
      l?.map (n, ·)
    if lvlSubst.isEmpty then e
    else e.instantiateLevelParams (lvlSubst.map (·.1)) (lvlSubst.map (·.2))

private def shouldUnfoldConstByRules (rulesRev : Array (Bool × Sum Name SimpTheorems))
    (declName : Name) : Bool := Id.run do
  for (pos, entry) in rulesRev do
    match entry with
    | .inl c =>
      if c == declName then
        return pos
    | .inr thms =>
      if simpTheoremsUnfolds thms declName then
        return pos
  return false

private structure StructState where
  vars   : Array (Option Expr)
  levels : Array (Option Level)

private abbrev StructM := StateT StructState MetaM

private structure StructCtx where
  pat          : ExprPattern
  flags        : ResolvedExprMatchFlags
  itemRulesRev : Array (Bool × Sum Name SimpTheorems)
  posFVars     : Array FVarId
  negFVars     : Array FVarId
  hasUnfolding : Bool

private def StructCtx.shouldUnfoldConst (ctx : StructCtx) (declName : Name) : Bool :=
  shouldUnfoldConstByRules ctx.itemRulesRev declName

private def StructCtx.shouldUnfoldFVar (ctx : StructCtx) (fv : FVarId) : Bool :=
  if ctx.posFVars.contains fv then true
  else if ctx.negFVars.contains fv then false
  else ctx.flags.zeta

private def tryCheckpoint (act : StructM Bool) : StructM Bool := do
  let saved ← get
  if ← act then
    return true
  set saved
  return false

private def withIncStructRecDepth (act : StructM α) : StructM α := fun s =>
  withIncRecDepth (act s)

private def isProofSafe (t : Expr) : MetaM Bool := do
  try isProof t catch _ => return false

private def inferTypeSafe (t : Expr) : MetaM (Option Expr) := do
  try
    let ty ← inferType t
    some <$> instantiateMVarsIfNeeded ty
  catch _ => return none

private def matchLevel (ctx : StructCtx) (isPat : Bool) (u₁ u₂ : Level) : StructM Bool := do
  let l₁ := u₁.normalize
  let l₂ := u₂.normalize
  if l₁ == l₂ && (!isPat || !levelHasPatParam ctx.pat.levelParams l₁) then
    return true
  go l₁ l₂
where
  go : Level → Level → StructM Bool
    | .zero,       .zero       => return true
    | .succ a,     .succ b     => go a b
    | .max a₁ b₁,  .max a₂ b₂  => go a₁ a₂ <&&> go b₁ b₂
    | .imax a₁ b₁, .imax a₂ b₂ => go a₁ a₂ <&&> go b₁ b₂
    | .param n₁,   l₂          => do
      if isPat then
        if let some idx := ctx.pat.levelParams.idxOf? n₁ then
          match (← get).levels.getD idx none with
          | none =>
            modify fun st => { st with levels := st.levels.setIfInBounds idx (some l₂) }
            return true
          | some boundL =>
            return boundL == l₂
      return Level.param n₁ == l₂
    | .mvar m₁,    .mvar m₂    => return m₁ == m₂
    | _,           _           => return false

private def matchLevelList (ctx : StructCtx) (isPat : Bool) : List Level → List Level → StructM Bool
  | [],      []      => return true
  | u :: us, v :: vs => matchLevel ctx isPat u v <&&> matchLevelList ctx isPat us vs
  | _,       _       => return false

private def allDistinct (xs : Array Expr) : Bool := Id.run do
  for h₁ : i in *...xs.size do
    for h₂ : j in (i + 1)...xs.size do
      if xs[i] == xs[j] then
        return false
  return true

private def unfoldConstStep? (ctx : StructCtx) (t : Expr) : MetaM (Option Expr) := do
  let .const cname us := t.getAppFn | return none
  unless ctx.shouldUnfoldConst cname do return none
  let some cinfo := (← getEnv).find? cname | return none
  unless cinfo.hasValue && cinfo.levelParams.length == us.length do return none
  let val ← instantiateValueLevelParams cinfo us
  return some (val.betaRev t.getAppRevArgs)

private def unfoldFVarStep? (ctx : StructCtx) (t : Expr) (lets : Array LetEntry) :
    MetaM (Option Expr) := do
  let .fvar fv := t.getAppFn | return none
  unless ctx.shouldUnfoldFVar fv do return none
  let val? ← match lets.find? (·.fv == fv) with
    | some entry => pure (some entry.val)
    | none =>
      match ← fv.findDecl? with
      | some decl =>
        match decl.value? (allowNondep := false) with
        | some v => some <$> instantiateMVarsIfNeeded v
        | none   => pure none
      | none => pure none
  let some val := val? | return none
  return some (mkAppN val t.getAppArgs)

-- Non-terminating in general because arbitrary unfolding / projection chains may diverge;
-- guarded dynamically by `withIncRecDepth`.
private partial def reduceProjTarget (ctx : StructCtx) (c : Expr) (lets : Array LetEntry) :
    MetaM Expr :=
  withIncRecDepth do
    let c ← resolveHeadMVar c
    if ctx.flags.beta && c.isHeadBetaTarget then
      return ← reduceProjTarget ctx c.headBeta lets
    if let .proj _ i inner := c then
      let inner' ← reduceProjTarget ctx inner lets
      if let some projected ← projectCore? inner' i then
        return ← reduceProjTarget ctx projected lets
    if let some unfolded ← unfoldFVarStep? ctx c lets then
      return ← reduceProjTarget ctx unfolded lets
    if let some unfolded ← unfoldConstStep? ctx c then
      return ← reduceProjTarget ctx unfolded lets
    return c

private def etaExpandOne? (ctx : StructCtx) (t : Expr) : MetaM (Option Expr) := do
  try
    let ty ← instantiateMVarsIfNeeded (← inferType t)
    let ty := ty.consumeMData
    if let .forallE x d _ bi := ty then
      return some (mkLambda x bi d (mkApp t (mkBVar 0)))
    if let some ty' ← unfoldConstStep? ctx ty then
      if let .forallE x d _ bi := ty' then
        return some (mkLambda x bi d (mkApp t (mkBVar 0)))
    return none
  catch _ => return none

private def isInstArgAt (f : Expr) : MetaM Bool := do
  if f.hasLooseBVars then
    return false
  try
    let argIdx := f.getAppNumArgs
    let fi ← getFunInfoNArgs f.getAppFn (argIdx + 1)
    return (fi.paramInfo[argIdx]?).any (·.binderInfo.isInstImplicit)
  catch _ =>
    return false

private def matchInstArgDefEq (ctx : StructCtx) (pa f a : Expr) : StructM Bool := do
  unless ctx.flags.inst && !a.hasLooseBVars do
    return false
  unless ← isInstArgAt f do
    return false
  let st ← get
  let paVar := substAssigned pa st.vars ctx.pat.numVars
  if paVar.hasLooseBVars then
    return false
  let paInst := substAssignedLevels paVar ctx.pat.levelParams st.levels
  withNewMCtxDepth <| withTransparency .instances do
    if ctx.pat.levelParams.isEmpty || !hasPatLevelParam ctx.pat.levelParams paInst then
      isDefEq paInst a
    else
      let mut unassignedNames : List Name := []
      let mut unassignedIdxs : List Nat := []
      let mut idx := 0
      for p in ctx.pat.levelParams do
        if (st.levels.getD idx none).isNone then
          unassignedNames := p :: unassignedNames
          unassignedIdxs := idx :: unassignedIdxs
        idx := idx + 1
      let fresh ← unassignedNames.mapM fun _ => mkFreshLevelMVar
      let paPrepared := paInst.instantiateLevelParams unassignedNames fresh
      if !(← isDefEq paPrepared a) then
        return false
      let resolved ← fresh.mapM instantiateLevelMVars
      for (lIdx, lvl) in unassignedIdxs.zip resolved do
        unless lvl.isMVar do
          modify fun s => { s with levels := s.levels.setIfInBounds lIdx (some lvl) }
      return true

-- Mutual structural matching can unfold definitions, beta-reduce, or project arbitrarily deeply;
-- guarded at runtime by `withIncStructRecDepth`.
mutual
  private partial def structAssign (ctx : StructCtx) (k : Nat) (rawV : Expr)
      (bound : Array Expr) (lets : Array LetEntry) (args : Array Expr := #[]) : StructM Bool := do
    let prev? := (← get).vars.getD k none
    if prev?.isNone && !ctx.pat.shouldCapture k then
      if bound.isEmpty || args.size == bound.size || !rawV.hasFVar then
        return true
      let wrapped := rewrapLets rawV lets
      return !wrapped.hasAnyFVar (bound.contains <| .fvar ·)
    let wrapped := rewrapLets rawV lets
    let val ←
      if args.isEmpty then
        pure wrapped
      else
        let mut lctx ← getLCtx
        let mut changed := false
        for arg in args do
          if let .fvar fv := arg then
            if let some d := lctx.find? fv then
              if d.isLet (allowNondep := true) then
                lctx := lctx.modifyLocalDecl fv fun decl =>
                  .cdecl decl.index decl.fvarId decl.userName decl.type .default decl.kind
                changed := true
        let lamVal ←
          if changed then
            withLCtx' lctx <| mkLambdaFVars args wrapped
          else
            mkLambdaFVars args wrapped
        pure lamVal.eta
    if !bound.isEmpty && args.size < bound.size && val.hasFVar then
      if val.hasAnyFVar (bound.contains <| .fvar ·) then
        return false
    match prev? with
    | none =>
      modify fun st => { st with vars := st.vars.setIfInBounds k (some val) }
      return true
    | some v' =>
      if eqModMData v' val then
        return true
      let rhs := if args.isEmpty then rawV else val
      let rhsLets := if args.isEmpty then lets else #[]
      return ← tryCheckpoint (structGo ctx v' rhs bound rhsLets (isPat := false) false)

  private partial def structDirectMatch (ctx : StructCtx) (pe e : Expr)
      (bound : Array Expr) (lets : Array LetEntry) (isPat isOrigPat : Bool) : StructM Bool := do
    match pe, e with
    | .app pf pa, .app f a =>
      if !(← structGo ctx pf f bound lets isPat isOrigPat) then
        return false
      if ← tryCheckpoint (structGo ctx pa a bound lets isPat isOrigPat) then
        return true
      if isPat then
        return ← tryCheckpoint (matchInstArgDefEq ctx pa f a)
      return false
    | .forallE _ pd pb _, .forallE x d b bi
    | .lam _ pd pb _,     .lam x d b bi =>
      if !(← structGo ctx pd d bound lets isPat isOrigPat) then return false
      withLocalDecl x bi d fun y =>
        structGo ctx (pb.instantiate1 y) (b.instantiate1 y) (bound.push y) lets isPat isOrigPat
    | .letE _ pt pv pb _, .letE x t v b nondep =>
      if !(← structGo ctx pt t bound lets isPat isOrigPat) then return false
      if !(← structGo ctx pv v bound lets isPat isOrigPat) then return false
      withLetDecl x t v (nondep := nondep) fun y =>
        structGo ctx (pb.instantiate1 y) (b.instantiate1 y) (bound.push y) lets isPat isOrigPat
    | .proj sn₁ i₁ pe', .proj sn₂ i₂ e' =>
      if sn₁ != sn₂ || i₁ != i₂ then return false
      structGo ctx pe' e' bound lets isPat isOrigPat
    | .const c₁ us₁, .const c₂ us₂ =>
      if c₁ != c₂ then return false
      matchLevelList ctx isPat us₁ us₂
    | .sort u₁, .sort u₂ => matchLevel ctx isPat u₁ u₂
    | .lit l₁,  .lit l₂  => return l₁ == l₂
    | .fvar f₁, .fvar f₂ => return f₁ == f₂
    | .mvar m₁, .mvar m₂ => return m₁ == m₂
    | _,        _        => return pe == e

  private partial def matchProofIrrel (ctx : StructCtx) (pe e : Expr)
      (bound : Array Expr) (lets : Array LetEntry) (isPat isOrigPat : Bool) : StructM Bool := do
    if pe.hasLooseBVars || e.hasLooseBVars then
      return false
    if isPat && isOrigPat && ctx.pat.precomputed && !pe.hasFVar &&
        !hasPatLevelFast ctx.pat true pe then
      let some peTy := ctx.pat.closedProofs[pe]? | return false
      unless ← isProofSafe e do return false
      let some eTy ← inferTypeSafe e | return false
      return ← tryCheckpoint (structGo ctx peTy eTy bound lets (isPat := false) false)
    let st ← get
    let peResolved :=
      if isPat then substAssignedLevels pe ctx.pat.levelParams st.levels else pe
    unless (← isProofSafe e) && (← isProofSafe peResolved) do
      return false
    let some peTy ← inferTypeSafe peResolved | return false
    let some eTy ← inferTypeSafe e | return false
    tryCheckpoint (structGo ctx peTy eTy bound lets
      (isPat := isPat && !ctx.pat.levelParams.isEmpty) false)

  private partial def structGo (ctx : StructCtx) (pe e : Expr)
      (bound : Array Expr) (lets : Array LetEntry)
      (isPat : Bool) (isOrigPat : Bool := isPat) : StructM Bool :=
    withIncStructRecDepth do
      let pe := pe.consumeMData
      let e ← resolveHeadMVar e
      if isPat then
        if let .bvar i := pe.getAppFn then
          let k := ctx.pat.numVars - 1 - i
          let args := pe.getAppArgs
          if args.isEmpty then
            return ← structAssign ctx k e bound lets
          if !ctx.pat.firstOrder.getD k false && args.all bound.contains && allDistinct args then
            return ← structAssign ctx k e bound lets args
      if !pe.hasLooseBVars && pe == e then
        if !isPat || !hasPatLevelFast ctx.pat isOrigPat pe then
          return true
      if ← tryCheckpoint (structDirectMatch ctx pe e bound lets isPat isOrigPat) then
        return true
      if ← matchProofIrrel ctx pe e bound lets isPat isOrigPat then
        return true
      unless ctx.hasUnfolding do
        return false
      -- Lazy look-through on `e` and (if items/flags allow or pinned head) `pe`.
      if ctx.flags.zeta then
        if let .letE x t v b nondep := e then
          if ← tryCheckpoint (withLetDecl x t v (nondep := nondep) fun y =>
              let lets' := lets.push { fv := y.fvarId!, userName := x, type := t, val := v, nondep }
              structGo ctx pe (b.instantiate1 y) bound lets' isPat isOrigPat) then
            return true
      if let some e' ← unfoldFVarStep? ctx e lets then
        if ← tryCheckpoint (structGo ctx pe e' bound lets isPat isOrigPat) then
          return true
      if ctx.flags.beta && e.isHeadBetaTarget then
        if ← tryCheckpoint (structGo ctx pe e.headBeta bound lets isPat isOrigPat) then
          return true
      if ctx.flags.proj then
        if let .proj s i c := e then
          let c' ← reduceProjTarget ctx c lets
          if ctx.flags.zeta then
            if let .letE x t v b nondep := c' then
              if ← tryCheckpoint (structGo ctx pe (mkLet x t v (mkProj s i b) nondep)
                  bound lets isPat isOrigPat) then
                return true
          if let some projected ← projectCore? c' i then
            if ← tryCheckpoint (structGo ctx pe projected bound lets isPat isOrigPat) then
              return true
      if let some e' ← unfoldConstStep? ctx e then
        if ← tryCheckpoint (structGo ctx pe e' bound lets isPat isOrigPat) then
          return true
      if ctx.flags.eta then
        if !pe.isLambda && e.isLambda then
          let eEta := e.eta
          if eEta != e then
            if ← tryCheckpoint (structGo ctx pe eEta bound lets isPat isOrigPat) then
              return true
          if let some peExp ← etaExpandOne? ctx pe then
            if ← tryCheckpoint (structGo ctx peExp e bound lets isPat false) then
              return true
        if pe.isLambda && !e.isLambda then
          if let some eExp ← etaExpandOne? ctx e then
            if ← tryCheckpoint (structGo ctx pe eExp bound lets isPat isOrigPat) then
              return true
      if isPat && pe.isApp then
        if let .bvar i := pe.getAppFn then
          let k := ctx.pat.numVars - 1 - i
          if let some headVal := (← get).vars.getD k none then
            let peApplied := mkAppN headVal pe.getAppArgs
            if ← tryCheckpoint (structGo ctx peApplied e bound lets (isPat := true) false) then
              return true
      if let some pe' ← unfoldFVarStep? ctx pe #[] then
        if ← tryCheckpoint (structGo ctx pe' e bound lets isPat false) then
          return true
      if ctx.flags.beta && pe.isHeadBetaTarget then
        if ← tryCheckpoint (structGo ctx pe.headBeta e bound lets isPat false) then
          return true
      if ctx.flags.zeta then
        if let .letE _ _ pv pb _ := pe then
          if ← tryCheckpoint (structGo ctx (pb.instantiate1 pv) e bound lets isPat false) then
            return true
      if ctx.flags.proj then
        if let .proj _ i pc := pe then
          let pc' ← reduceProjTarget ctx pc #[]
          if let some projected ← projectCore? pc' i then
            if ← tryCheckpoint (structGo ctx projected e bound lets isPat false) then
              return true
      if let some pe' ← unfoldConstStep? ctx pe then
        if ← tryCheckpoint (structGo ctx pe' e bound lets isPat false) then
          return true
      return false
end

private def matchStructural? (p : ExprPattern) (rel : ResolvedExprMatchRel)
    (pinIdxs : Array Nat) (pins : Array Expr) (e : Expr) : MetaM (Option (Array Expr)) := do
  let n := p.numVars
  let ctx : StructCtx := {
    pat          := p
    flags        := rel.flags
    itemRulesRev := rel.itemRulesRev
    posFVars     := rel.posFVars
    negFVars     := rel.negFVars
    hasUnfolding := rel.hasUnfolding
  }
  let mut initVars : Array (Option Expr) := .replicate n none
  for (idx, rawPin) in pinIdxs.zip pins do
    let pin ← instantiateMVarsIfNeeded rawPin
    initVars := initVars.setIfInBounds idx (some pin)
  let initState : StructState := {
    vars   := initVars
    levels := .replicate p.levelParams.length none
  }
  let (ok, st) ← (structGo ctx p.body e #[] #[] (isPat := true) true).run initState
  if !ok then
    return none
  return p.namedIdx.mapM fun i => st.vars.getD i none

private def withLocalDefItems (zetaFlag : Bool) (posFVars negFVars : Array FVarId)
    (x : MetaM α) : MetaM α := do
  if zetaFlag then
    if negFVars.isEmpty then
      return ← x
    let mut lctx ← getLCtx
    for fv in negFVars do
      if let some d := lctx.find? fv then
        if d.isLet (allowNondep := true) then
          lctx := lctx.modifyLocalDecl fv fun decl =>
            .cdecl decl.index decl.fvarId decl.userName decl.type .default decl.kind
    withLCtx' lctx (withFreshCache x)
  else if posFVars.isEmpty then
    if (← read).zetaDeltaSet.isEmpty then
      x
    else
      withFreshCache <| withReader (fun ctx => { ctx with zetaDeltaSet := {} }) x
  else
    let mut posSet : FVarIdSet := {}
    for fv in posFVars do
      posSet := posSet.insert fv
    withFreshCache <| withReader (fun ctx => { ctx with zetaDeltaSet := posSet }) x

private def engineTransparency : ExprMatchEngine → TransparencyMode
  | .structural => .none
  | .reducible  => .reducible
  | .instances  => .instances
  | .defeq      => .default
  | .sym        => .reducible

private def withRelDefEqConfig (transparency : TransparencyMode)
    (flags : ResolvedExprMatchFlags) (withZeta withZetaDelta : Bool)
    (k : MetaM α) : MetaM α :=
  withOptions (fun opts =>
    if !flags.proj then opts.setBool `backward.isDefEq.lazyWhnfCore false else opts) <|
  withConfig (fun cfg => { cfg with
    transparency
    beta       := flags.beta
    zeta       := withZeta
    zetaDelta  := withZetaDelta
    zetaHave   := withZeta
    zetaUnused := withZeta
    proj       := if flags.proj then .yesWithDelta else .no
    etaStruct  := if flags.eta then .all else .none
  }) k

private def runDefEqOnce (p : ExprPattern) (pinIdxs : Array Nat) (pins : Array Expr)
    (transparency : TransparencyMode) (flags : ResolvedExprMatchFlags)
    (withZeta withZetaDelta : Bool) (curE : Expr) : MetaM (Option (Array Expr)) := do
  withRelDefEqConfig transparency flags withZeta withZetaDelta do
    withNewMCtxDepth do
      let us ← p.levelParams.mapM fun _ => mkFreshLevelMVar
      let lam := p.lam.instantiateLevelParams p.levelParams us
      let mut subst : Array Expr := Array.mkEmpty p.numVars
      let mut cur := lam
      for i in *...p.numVars do
        match cur with
        | .lam _ d b _ =>
          if let some pinPos := pinIdxs.idxOf? i then
            subst := subst.push (pins.getD pinPos default)
          else
            let ty := d.instantiateRevRange 0 subst.size subst
            let mv ← mkFreshExprMVar (some ty)
            subst := subst.push mv
          cur := b
        | _ => break
      let pe := cur.instantiateRevRange 0 subst.size subst
      unless ← isDefEq pe curE do
        return none
      let namedVals ← p.namedIdx.mapM fun idx =>
        instantiateMVarsIfNeeded (subst.getD idx default)
      if ← namedVals.anyM hasAssignableMVar then
        return none
      return some namedVals

private def countLeadingLetMData : Expr → Nat
  | .mdata _ b      => countLeadingLetMData b + 1
  | .letE _ _ _ b _ => countLeadingLetMData b + 1
  | _               => 0

private def isPatHoleOrBVar (numVars : Nat) (pinIdxs : Array Nat)
    (pe : Expr) (patDepth : Nat) : Bool :=
  match pe with
  | .bvar _ => true
  | _ =>
    if pe.looseBVarRange <= patDepth then false
    else match pe.getAppFn.consumeMData with
      | .bvar i =>
        if i >= patDepth && i - patDepth < numVars then
          !pinIdxs.contains (numVars - 1 - (i - patDepth))
        else
          false
      | _ => false

private def isCompositePat : Expr → Bool
  | .app .. | .lam .. | .forallE .. | .letE .. | .proj .. => true
  | _ => false

private def needsWhnfForComposite (pe e : Expr) : Bool :=
  match pe, e with
  | .app .., .app .. =>
    match pe.getAppFn.consumeMData, e.getAppFn.consumeMData with
    | .const c₁ _, .const c₂ _ => c₁ != c₂
    | _,           .lam .. | _, .letE .. | _, .proj .. | _, .mvar .. => true
    | _,           _ => false
  | .app ..,     _ => true
  | .lam ..,     .lam .. => false
  | .lam ..,     _ => true
  | .forallE .., .forallE .. => false
  | .forallE .., _ => true
  | .letE ..,    .letE .. => false
  | .letE ..,    _ => true
  | .proj ..,    .proj .. => false
  | .proj ..,    _ => true
  | _,           _ => false

private def whnfNoZeta (transparency : TransparencyMode) (flags : ResolvedExprMatchFlags)
    (e : Expr) : MetaM Expr :=
  withRelDefEqConfig transparency flags false false (whnf e)

mutual
  private def liftInspectedLetsStep (numVars : Nat) (pinIdxs : Array Nat)
      (transparency : TransparencyMode) (flags : ResolvedExprMatchFlags)
      (pe curE : Expr) (patDepth whnfFuel : Nat) (lets : Array LetEntry)
      (k : Expr → Array LetEntry → MetaM (Option (Array Expr))) :
      MetaM (Option (Array Expr)) :=
    match pe with
    | .app pf pa =>
      match curE with
      | .app ef ea =>
        liftInspectedLetsGo numVars pinIdxs transparency flags pf ef patDepth whnfFuel
          (countLeadingLetMData ef) lets fun ef' lets₁ =>
            liftInspectedLetsGo numVars pinIdxs transparency flags pa ea patDepth whnfFuel
              (countLeadingLetMData ea) lets₁ fun ea' lets₂ =>
                k (curE.updateApp! ef' ea') lets₂
      | _ => k curE lets
    | .lam _ pd pb _ =>
      match curE with
      | .lam _ t b _ =>
        liftInspectedLetsGo numVars pinIdxs transparency flags pd t patDepth whnfFuel
          (countLeadingLetMData t) lets fun t' lets₁ =>
            liftInspectedLetsGo numVars pinIdxs transparency flags pb b (patDepth + 1) whnfFuel
              (countLeadingLetMData b) lets₁ fun b' lets₂ =>
                k (curE.updateLambdaE! t' b') lets₂
      | _ => k curE lets
    | .forallE _ pd pb _ =>
      match curE with
      | .forallE _ t b _ =>
        liftInspectedLetsGo numVars pinIdxs transparency flags pd t patDepth whnfFuel
          (countLeadingLetMData t) lets fun t' lets₁ =>
            liftInspectedLetsGo numVars pinIdxs transparency flags pb b (patDepth + 1) whnfFuel
              (countLeadingLetMData b) lets₁ fun b' lets₂ =>
                k (curE.updateForallE! t' b') lets₂
      | _ => k curE lets
    | .letE _ pt pv pb _ =>
      match curE with
      | .letE _ t v b nd =>
        liftInspectedLetsGo numVars pinIdxs transparency flags pt t patDepth whnfFuel
          (countLeadingLetMData t) lets fun t' lets₁ =>
            liftInspectedLetsGo numVars pinIdxs transparency flags pv v patDepth whnfFuel
              (countLeadingLetMData v) lets₁ fun v' lets₂ =>
                liftInspectedLetsGo numVars pinIdxs transparency flags pb b (patDepth + 1) whnfFuel
                  (countLeadingLetMData b) lets₂ fun b' lets₃ =>
                    k (curE.updateLet! t' v' b' nd) lets₃
      | _ => k curE lets
    | .proj sn₁ i₁ pe' =>
      match curE with
      | .proj sn₂ i₂ e' =>
        if sn₁ != sn₂ || i₁ != i₂ then
          k curE lets
        else
          liftInspectedLetsGo numVars pinIdxs transparency flags pe' e' patDepth whnfFuel
            (countLeadingLetMData e') lets fun e'' lets' =>
              k (curE.updateProj! e'') lets'
      | _ => k curE lets
    | _ => k curE lets
  termination_by (sizeOf pe, whnfFuel, 0, 0)

  private def liftInspectedLetsGo (numVars : Nat) (pinIdxs : Array Nat)
      (transparency : TransparencyMode) (flags : ResolvedExprMatchFlags)
      (pe curE : Expr) (patDepth whnfFuel letFuel : Nat) (lets : Array LetEntry)
      (k : Expr → Array LetEntry → MetaM (Option (Array Expr))) :
      MetaM (Option (Array Expr)) :=
    match pe with
    | .mdata _ pb =>
      liftInspectedLetsGo numVars pinIdxs transparency flags pb curE patDepth whnfFuel
        letFuel lets k
    | pe => do
      if isPatHoleOrBVar numVars pinIdxs pe patDepth then
        return ← k curE lets
      let isPatLet := match pe with | .letE .. => true | _ => false
      match letFuel, curE with
      | n + 1, .mdata _ inner =>
        return ← liftInspectedLetsGo numVars pinIdxs transparency flags pe inner patDepth whnfFuel n
          lets fun inner' lets' => k (curE.updateMData! inner') lets'
      | n + 1, .letE x t v b nondep =>
        if !isPatLet && !t.hasLooseBVars && !v.hasLooseBVars then
          -- Keep `nondep := false` in `LCtx` so fallback `zetaDelta` can still unfold `have`s if
          -- needed, while recording the original `nondep` on `LetEntry` for `rewrapLets`.
          return ← withLetDecl x t v (nondep := false) fun fv =>
            let entry : LetEntry := { fv := fv.fvarId!, userName := x, type := t, val := v, nondep }
            liftInspectedLetsGo numVars pinIdxs transparency flags pe (b.instantiate1 fv) patDepth
              whnfFuel n (lets.push entry) k
      | _, _ => pure ()
      unless isCompositePat pe do
        return ← k curE lets
      match whnfFuel with
      | fuel + 1 =>
        if needsWhnfForComposite pe curE then
          let eW ← whnfNoZeta transparency flags curE
          if eW != curE then
            return ← liftInspectedLetsGo numVars pinIdxs transparency flags pe eW patDepth fuel
              (countLeadingLetMData eW) lets k
      | 0 => pure ()
      liftInspectedLetsStep numVars pinIdxs transparency flags pe curE patDepth whnfFuel
        lets k
  termination_by (sizeOf pe, whnfFuel, 1, letFuel)
end

private def mayIntroduceLet (env : Environment) (fuel : Nat) (e : Expr) : Nat × Bool :=
  if e.hasFVar then
    (0, true)
  else
    match fuel with
    | 0 => (0, true)
    | fuel + 1 =>
      match e with
      | .letE .. | .fvar _ | .proj .. => (fuel, true)
      | .const c _ =>
        match env.find? c with
        | some (.defnInfo _) => (fuel, true)
        | _ => (fuel, false)
      | .mdata _ b => mayIntroduceLet env fuel b
      | .app f a =>
        let (fuel, hit) := mayIntroduceLet env fuel f
        if hit then (fuel, true) else mayIntroduceLet env fuel a
      | .lam _ t b _ | .forallE _ t b _ =>
        let (fuel, hit) := mayIntroduceLet env fuel t
        if hit then (fuel, true) else mayIntroduceLet env fuel b
      | .bvar _ | .sort _ | .lit _ | .mvar _ => (fuel, false)

private def withRelUnfoldRules (rel : ResolvedExprMatchRel) (k : MetaM α) : MetaM α :=
  withLocalDefItems rel.flags.zeta rel.posFVars rel.negFVars do
    if rel.itemRulesRev.isEmpty then
      k
    else
      let pred (cfg : Config) (info : ConstantInfo) : CoreM Bool := do
        for (pos, entry) in rel.itemRulesRev do
          match entry with
          | .inl c =>
            if c == info.name then
              return pos
          | .inr thms =>
            if simpTheoremsUnfolds thms info.name then
              return pos
        canUnfoldDefault cfg info
      withCanUnfoldPred pred k

private def matchDefEq? (p : ExprPattern) (rel : ResolvedExprMatchRel)
    (pinIdxs : Array Nat) (pins : Array Expr) (e : Expr) : MetaM (Option (Array Expr)) := do
  let transparency := engineTransparency rel.engine
  let env ← getEnv
  let e ← instantiateMVarsIfNeeded e
  let pins ← pins.mapM instantiateMVarsIfNeeded
  let runAt (target : Expr) (liftedLets : Array LetEntry) : MetaM (Option (Array Expr)) := do
    let res ←
      if !rel.flags.zeta && rel.posFVars.isEmpty then
        runDefEqOnce p pinIdxs pins transparency rel.flags false false target
      else
        match ← runDefEqOnce p pinIdxs pins transparency rel.flags false false target with
        | some σ => pure (some σ)
        | none   =>
          -- Skip the zeta fallback when no `let`s were lifted and bounded inspection finds no
          -- `fvar`s, `letE`s, projections, or unfoldable definitions that could expose a `let`.
          let needZeta := !liftedLets.isEmpty ||
            (mayIntroduceLet env 64 target).2 ||
            (mayIntroduceLet env 64 p.body).2 ||
            pins.any fun pin => (mayIntroduceLet env 64 pin).2
          if needZeta then
            runDefEqOnce p pinIdxs pins transparency rel.flags
              rel.flags.zeta rel.flags.zeta target
          else
            pure none
    return res.map fun σ =>
      if liftedLets.isEmpty then σ else σ.map (rewrapLets · liftedLets)
  let runCore :=
    if !rel.flags.zeta then
      runAt e #[]
    else
      liftInspectedLetsGo p.numVars pinIdxs transparency rel.flags p.body e 0 16
        (countLeadingLetMData e) #[] runAt
  withRelUnfoldRules rel runCore

/--
Match `p` with pre-resolved relation `rel` and direct pin values `pins` at `pinIdxs`, returning
bound values in `p.namedIdx` order. Does not re-resolve simp items or rebuild `p.lam` per call.

Under `.structural`, captured subterms are not deeply mvar-instantiated below head position (for
`O(|pattern|)` performance); callers inspecting captured values structurally should run
`instantiateMVars` if nested assigned metavariables need resolving.
-/
def ExprPattern.matchResolvedPins? (p : ExprPattern) (rel : ResolvedExprMatchRel)
    (pinIdxs : Array Nat) (pins : Array Expr) (e : Expr) : MetaM (Option (Array Expr)) := do
  match rel.engine with
  | .sym =>
    throwError "expr quotation `/sym` matching engine is not implemented yet (Spike B / B5)"
  | .structural =>
    matchStructural? p rel pinIdxs pins e
  | .reducible | .instances | .defeq =>
    matchDefEq? p rel pinIdxs pins e

/--
Match `p` against `e` under a pre-resolved relation `rel`. See `matchResolvedPins?` regarding
nested assigned metavariables in captured subterms.
-/
def ExprPattern.matchResolved? (p : ExprPattern) (rel : ResolvedExprMatchRel)
    (e : Expr) : MetaM (Option (Array Expr)) :=
  p.matchResolvedPins? rel #[] #[] e

/--
Match `p` against `e` under relation `rel` and optional runtime local-def unfold items.
Captured subterms under `.structural` are not deeply mvar-instantiated below head position; call
`instantiateMVars` if inspecting nested assigned metavariables structurally.
-/
def ExprPattern.match? (p : ExprPattern) (rel : ExprMatchRel) (e : Expr)
    (localItems : Array (Bool × Expr) := #[]) : MetaM (Option (Array Expr)) := do
  let r ← rel.resolve localItems
  p.matchResolvedPins? r #[] #[] e

/-- Project the `i`-th matched binder from `xs` with `Inhabited` fallback. -/
@[inline]
def ExprPattern.arg (xs : Array Expr) (i : Nat) : Expr :=
  xs.getD i default

/--
CPS matching combinator accepting a pre-resolved relation `rel`, avoiding per-call rule resolution
and pin lambda reconstruction. See `matchResolvedPins?` regarding nested assigned metavariables.
-/
@[inline]
def ExprPattern.matchResolvedOrElse {m : Type → Type v} [Monad m] [MonadLiftT MetaM m] {α : Type}
    (p : ExprPattern) (rel : ResolvedExprMatchRel) (pinIdxs : Array Nat) (pins : Array Expr)
    (e : Expr) (onMatch : Array Expr → m α) (onFail : Unit → m α) : m α := do
  match ← (p.matchResolvedPins? rel pinIdxs pins e : MetaM (Option (Array Expr))) with
  | some xs => onMatch xs
  | none    => onFail ()

/--
CPS matching combinator resolving `rel` via the runtime site cache keyed by `siteId`, pre-seeding
`pins` at `pinIdxs` directly without rebuilding `p.lam`, and invoking `onMatch` or `onFail`.
Captured subterms under `.structural` are not deeply mvar-instantiated below head position; call
`instantiateMVars` if inspecting nested assigned metavariables structurally.
-/
@[inline]
def ExprPattern.matchSiteOrElse {m : Type → Type v} [Monad m] [MonadLiftT MetaM m] {α : Type}
    (siteId : Name) (p : ExprPattern) (rel : ExprMatchRel) (pinIdxs : Array Nat)
    (pins : Array Expr) (localItems : Array (Bool × Expr)) (e : Expr)
    (onMatch : Array Expr → m α) (onFail : Unit → m α) : m α := do
  let r ← (rel.resolve localItems siteId : MetaM ResolvedExprMatchRel)
  match ← (p.matchResolvedPins? r pinIdxs pins e : MetaM (Option (Array Expr))) with
  | some xs => onMatch xs
  | none    => onFail ()

/--
CPS matching combinator used by native `match`/`let`/`if let` compilation on `Expr` patterns.
Pre-seeds `pins` at `pinIdxs` directly without rebuilding `p.lam`, resolves `rel`, matches against
`e`, and invokes `onMatch` with the bound `?`-variables or `onFail ()` if matching fails.
See `matchSiteOrElse` regarding nested assigned metavariables in captured subterms.
-/
@[inline]
def ExprPattern.matchOrElse {m : Type → Type v} [Monad m] [MonadLiftT MetaM m] {α : Type}
    (p : ExprPattern) (rel : ExprMatchRel) (pinIdxs : Array Nat) (pins : Array Expr)
    (localItems : Array (Bool × Expr)) (e : Expr)
    (onMatch : Array Expr → m α) (onFail : Unit → m α) : m α :=
  p.matchSiteOrElse .anonymous rel pinIdxs pins localItems e onMatch onFail

/-! ## `ExprTemplate` and Runtime Term Building -/

/-- Role of an abstracted parameter inside a compiled `ExprTemplate`. -/
inductive ExprTemplateVarKind where
  /-- Runtime `$e` splice parameter receiving `splices[splicePos]`. -/
  | splice (splicePos : Nat)
  /-- Explicit `?h` / `?_` hole materialized as a fresh `.syntheticOpaque` mvar at runtime. -/
  | hole (userName? : Option Name)
  /-- Dependent type-class instance synthesized at runtime once input types are resolved. -/
  | tc
  /-- Auxiliary type or `outParam` parameter inferred from splice types and TC resolution. -/
  | infer
  deriving Inhabited, BEq, Hashable, Repr

/--
Compiled closed template `lam = fun x₀ … xₙ₋₁ => body` (modulo `levelParams`) produced by a
term-position `` `(expr[rel]| t) `` quotation.
-/
structure ExprTemplate where
  /-- Universe parameter names abstracted in `lam`. -/
  levelParams : List Name
  /-- Template expression wrapped in `varKinds.size` outer lambdas. -/
  lam         : Expr
  /-- Classification of each outer lambda parameter during instantiation. -/
  varKinds    : Array ExprTemplateVarKind
  deriving Inhabited, BEq, Hashable

/--
Inspect a pending type-class goal `goalType`. Returns `some (inputExprs, inputLevels)` listing
the non-`outParam` argument expressions (plus outer binder domains) and non-output universe levels,
or `none` if the goal head is not a known constant.
-/
def inspectClassGoalInputs? (goalType : Expr) :
    MetaM (Option (Array Expr × Array Level)) := do
  forallTelescopeReducing goalType fun xs typeBody => do
    let typeBody ← whnf typeBody
    let mut inExprs : Array Expr := #[]
    for x in xs do
      inExprs := inExprs.push (← x.fvarId!.getType)
    let .const declName us := typeBody.getAppFn
      | return none
    let env ← getEnv
    let outArgs := (getOutParamPositions? env declName).getD #[]
    let outLvls := (getOutLevelParamPositions? env declName).getD #[]
    let mut inLvls : Array Level := #[]
    for (u, i) in us.zipIdx do
      unless outLvls.contains i do
        inLvls := inLvls.push u
    let args := typeBody.getAppArgs
    for h : i in *...args.size do
      unless outArgs.contains i do
        inExprs := inExprs.push args[i]
    return some (inExprs, inLvls)

private def peelTemplateLambdas (n : Nat) (e : Expr)
    (doms : Array Expr := #[]) : Array Expr × Expr :=
  match n, e with
  | k + 1, .lam _ d b _ => peelTemplateLambdas k b (doms.push d)
  | _,     _            => (doms, e)

private def levelHasTempMVar (mctx : MetavarContext) (baseDepth : Nat) : Level → Bool
  | .mvar id  => mctx.getLevelDepth id > baseDepth
  | .succ u   => levelHasTempMVar mctx baseDepth u
  | .max u v  => levelHasTempMVar mctx baseDepth u || levelHasTempMVar mctx baseDepth v
  | .imax u v => levelHasTempMVar mctx baseDepth u || levelHasTempMVar mctx baseDepth v
  | .zero | .param _ => false

private def hasTempMVar (mctx : MetavarContext) (baseDepth : Nat) (e : Expr) : Bool :=
  if !e.hasMVar then
    false
  else
    (e.find? fun
      | .mvar id    => (mctx.findDecl? id).any (·.depth > baseDepth)
      | .sort u     => levelHasTempMVar mctx baseDepth u
      | .const _ us => us.any (levelHasTempMVar mctx baseDepth)
      | _           => false).isSome

private def isTCGoalReady (baseDepth : Nat) (tcTy : Expr) : MetaM Bool := do
  let mctx ← getMCtx
  match ← inspectClassGoalInputs? tcTy with
  | none => return !hasTempMVar mctx baseDepth tcTy
  | some (inExprs, inLvls) =>
    return !(inExprs.any (hasTempMVar mctx baseDepth) ||
      inLvls.any (levelHasTempMVar mctx baseDepth))

private def synthTCWithError (tcMV : MVarId) (tcTy : Expr) : MetaM Unit := do
  let inst ←
    try
      synthInstance tcTy
    catch ex =>
      throwError "expr quotation failed to synthesize dependent instance{indentExpr tcTy}\n\
        {ex.toMessageData}"
  tcMV.assign inst

private def resolveReadyTCsGo (baseDepth : Nat) (fuel : Nat)
    (pending : Array MVarId) : MetaM (Array MVarId) := do
  if pending.isEmpty then
    return #[]
  match fuel with
  | 0 => return pending
  | fuel + 1 =>
    let mut stillPending : Array MVarId := #[]
    let mut progressed := false
    for tcMV in pending do
      let tcTy ← instantiateMVars (← tcMV.getDecl).type
      if ← isTCGoalReady baseDepth tcTy then
        synthTCWithError tcMV tcTy
        progressed := true
      else
        stillPending := stillPending.push tcMV
    if progressed && !stillPending.isEmpty then
      resolveReadyTCsGo baseDepth fuel stillPending
    else
      return stillPending

private def resolveReadyTCs (baseDepth : Nat) (pending : Array MVarId) :
    MetaM (Array MVarId) :=
  resolveReadyTCsGo baseDepth pending.size pending

/--
Instantiate a compiled `ExprTemplate` under a pre-resolved relation `rel` and runtime splice
values `splices`. Preserves caller pointer sharing and caller metavariables inside `splices`,
allocates zero metavariables for splices, checks splice types with `isDefEq` under `rel` (running
under `withNewMCtxDepth` so caller metavariables with unknown types are left unassigned and fail
the check cleanly if a concrete or mismatched expected type is required), synthesizes
splice-dependent type-class instances, and materializes fresh `.syntheticOpaque` metavariables in
the caller's `MCtx` for `?h` / `?_` holes.
-/
def ExprTemplate.instantiateResolved (tmpl : ExprTemplate) (rel : ResolvedExprMatchRel)
    (splices : Array Expr) : MetaM Expr := do
  if rel.engine == .sym then
    throwError "expr quotation `/sym` building engine is not implemented yet (Spike B / B5)"
  let n := tmpl.varKinds.size
  if n == 0 && tmpl.levelParams.isEmpty then
    return tmpl.lam
  let baseDepth := (← getMCtx).depth
  let transparency := engineTransparency rel.engine
  let (body, substAfterSplices, holePlans) ← withNewMCtxDepth do
    let us ← tmpl.levelParams.mapM fun _ => mkFreshLevelMVar
    let lam :=
      if us.isEmpty then tmpl.lam
      else tmpl.lam.instantiateLevelParams tmpl.levelParams us
    let (doms, body) := peelTemplateLambdas n lam
    let mut subst : Array Expr := Array.emptyWithCapacity doms.size
    let mut pendingTCs : Array MVarId := #[]
    let mut holePlaceholders : Array (Nat × MVarId × Option Name) := #[]
    for h : i in *...doms.size do
      let expTyRaw := doms[i].instantiateRevRange 0 subst.size subst
      let mut expTy ← instantiateMVars expTyRaw
      match tmpl.varKinds.getD i .infer with
      | .infer =>
        let mv ← mkFreshExprMVar (some expTy)
        subst := subst.push mv
      | .tc =>
        let mv ← mkFreshExprMVar (some expTy) .synthetic
        subst := subst.push mv
        pendingTCs := pendingTCs.push mv.mvarId!
      | .splice pos =>
        if !pendingTCs.isEmpty && hasTempMVar (← getMCtx) baseDepth expTy then
          pendingTCs ← resolveReadyTCs baseDepth pendingTCs
          expTy ← instantiateMVars expTy
        let val := splices.getD pos default
        if val.hasLooseBVars then
          throwError "expr quotation splice expression contains loose bound variable:\
            {indentExpr val}"
        let argTy ← instantiateMVars (← inferType val)
        let ok ← withRelUnfoldRules rel <|
          withRelDefEqConfig transparency rel.flags rel.flags.zeta rel.flags.zeta <|
            isDefEq argTy expTy
        unless ok do
          let expTyShown ← instantiateMVars expTy
          throwError "expr quotation splice type mismatch: argument{indentExpr val}\n\
            has type{indentExpr argTy}\nbut is expected to have type{indentExpr expTyShown}"
        subst := subst.push val
      | .hole userName? =>
        let mv ← mkFreshExprMVar (some expTy) .syntheticOpaque
        subst := subst.push mv
        holePlaceholders := holePlaceholders.push (i, mv.mvarId!, userName?)
    if !pendingTCs.isEmpty then
      pendingTCs ← resolveReadyTCs baseDepth pendingTCs
      for tcMV in pendingTCs do
        let tcTy ← instantiateMVars (← tcMV.getDecl).type
        if hasTempMVar (← getMCtx) baseDepth tcTy then
          throwError "expr quotation failed to resolve dependent instance{indentExpr tcTy}"
        synthTCWithError tcMV tcTy
    let mctx ← getMCtx
    for u in us do
      let u' ← instantiateLevelMVars u
      if levelHasTempMVar mctx baseDepth u' then
        throwError "expr quotation failed to resolve universe level at runtime"
    let body ← instantiateMVars body
    let mut finalSubst := subst
    for h : i in *...doms.size do
      match tmpl.varKinds.getD i .infer with
      | .infer | .tc =>
        let v ← instantiateMVars (finalSubst.getD i default)
        if hasTempMVar (← getMCtx) baseDepth v then
          throwError "expr quotation failed to resolve implicit argument at runtime:\
            {indentExpr v}"
        finalSubst := finalSubst.setIfInBounds i v
      | .splice _ | .hole _ => pure ()
    let holePlans ← holePlaceholders.mapM fun (idx, tmpId, userName?) => do
      let holeTy ← instantiateMVars (← tmpId.getDecl).type
      return (idx, tmpId, userName?, holeTy)
    return (body, finalSubst, holePlans)
  let mut finalSubst := substAfterSplices
  if !holePlans.isEmpty then
    let mctx ← getMCtx
    let mut tmpHoleMap : Std.HashMap MVarId Expr := {}
    for (idx, tmpId, userName?, rawHoleTy) in holePlans do
      let holeTy :=
        if rawHoleTy.hasExprMVar && !tmpHoleMap.isEmpty then
          rawHoleTy.replace fun
            | .mvar id => tmpHoleMap[id]?
            | _        => none
        else
          rawHoleTy
      if hasTempMVar mctx baseDepth holeTy then
        throwError "expr quotation failed to resolve hole type at runtime:{indentExpr holeTy}"
      let holeMV ← mkFreshExprMVar (some holeTy) .syntheticOpaque (userName?.getD .anonymous)
      tmpHoleMap := tmpHoleMap.insert tmpId holeMV
      finalSubst := finalSubst.setIfInBounds idx holeMV
  return body.instantiateRev finalSubst

/--
Instantiate a compiled `ExprTemplate`, resolving `rel` and optional runtime local `$x` items
through the runtime per-site cache keyed by `siteId`.
-/
def ExprTemplate.instantiateSite (siteId : Name) (tmpl : ExprTemplate) (rel : ExprMatchRel)
    (splices : Array Expr) (localItems : Array (Bool × Expr) := #[]) : MetaM Expr := do
  let r ← rel.resolve localItems siteId
  tmpl.instantiateResolved r splices

/--
General entry point to instantiate a compiled `ExprTemplate` under relation `rel`, runtime
`splices`, and optional local `$x` definition overrides.
-/
def ExprTemplate.instantiate (tmpl : ExprTemplate) (rel : ExprMatchRel)
    (splices : Array Expr) (localItems : Array (Bool × Expr) := #[]) : MetaM Expr :=
  ExprTemplate.instantiateSite .anonymous tmpl rel splices localItems

/-! ## `ExprContext` and Goal/Expression Sources -/

private inductive ExprContextFrame where
  | appFn      (parent arg : Expr)
  | appArg     (parent fn : Expr)
  | lamType    (parent body : Expr)
  | lamBody    (parent dom : Expr)
  | forallType (parent body : Expr)
  | forallBody (parent dom : Expr)
  | letType    (parent val body : Expr) (nondep : Bool)
  | letVal     (parent ty body : Expr) (nondep : Bool)
  | letBody    (parent ty val : Expr) (nondep : Bool)
  | mdata      (parent : Expr)
  | proj       (parent : Expr)
  deriving Inhabited

/--
Zipper-style context pointing from a closed subterm back to its enclosing root `Expr`.
Use `ExprContext.fill` to substitute a new expression into the hole while preserving unchanged
subtrees and pointer sharing.
-/
structure ExprContext where
  private frames : List ExprContextFrame := []
  deriving Inhabited

/-- Plug `replacement` into the hole represented by `ctx`, rebuilding to the root `Expr`. -/
def ExprContext.fill (ctx : ExprContext) (replacement : Expr) : Expr :=
  ctx.frames.foldl (init := replacement) fun cur frame =>
    match frame with
    | .appFn parent arg          => parent.updateApp! cur arg
    | .appArg parent fn          => parent.updateApp! fn cur
    | .lamType parent body       => parent.updateLambdaE! cur body
    | .lamBody parent dom        => parent.updateLambdaE! dom cur
    | .forallType parent body    => parent.updateForallE! cur body
    | .forallBody parent dom     => parent.updateForallE! dom cur
    | .letType parent val body nd => parent.updateLet! cur val body nd
    | .letVal parent ty body nd  => parent.updateLet! ty cur body nd
    | .letBody parent ty val nd  => parent.updateLet! ty val cur nd
    | .mdata parent              => parent.updateMData! cur
    | .proj parent               => parent.updateProj! cur

private def isExcludedFVar (except : List Expr) (fv : FVarId) : Bool :=
  except.any fun ex =>
    match ex.consumeMData with
    | .fvar id => id == fv
    | _        => false

/--
Collect non-implementation-detail local hypotheses `(hyp, type)` from the local context.
Returns hypotheses oldest first by default (or newest first when `reverse := true`), excluding any
fvar listed in `except`, with metavariables instantiated in `type`.
-/
def localHypTypes (reverse : Bool := false) (except : List Expr := []) :
    MetaM (Array (Expr × Expr)) := do
  let lctx ← getLCtx
  let mut res : Array (Expr × Expr) := #[]
  for decl in lctx do
    unless decl.isImplementationDetail || isExcludedFVar except decl.fvarId do
      let ty ← instantiateMVarsIfNeeded decl.type
      res := res.push (mkFVar decl.fvarId, ty)
  return if reverse then res.reverse else res

/--
Collect non-implementation-detail local declarations `(hyp, type, val?)` from the local context.
Returns declarations oldest first by default (or newest first when `reverse := true`), excluding
any fvar listed in `except`. Only dependent `let`-declarations yield `some val` (`have`
declarations yield `none`), with metavariables instantiated in `type` and `val`.
-/
def localHypDecls (reverse : Bool := false) (except : List Expr := []) :
    MetaM (Array (Expr × Expr × Option Expr)) := do
  let lctx ← getLCtx
  let mut res : Array (Expr × Expr × Option Expr) := #[]
  for decl in lctx do
    unless decl.isImplementationDetail || isExcludedFVar except decl.fvarId do
      let ty ← instantiateMVarsIfNeeded decl.type
      let val? ← match decl.value? (allowNondep := false) with
        | some v => some <$> instantiateMVarsIfNeeded v
        | none   => pure none
      res := res.push (mkFVar decl.fvarId, ty, val?)
  return if reverse then res.reverse else res

/--
Lazy stream of closed subterms of an `Expr`, each paired with its `ExprContext`.
Created by `subterms`. Supports `for (sub, ctx) in subterms e do ...` with early exit (`break`),
plus `.toArray` and `.toList`.
-/
structure Subterms where
  /-- Root expression to inspect. -/
  expr               : Expr
  /--
  Deduplicate structurally equal subterms via `ExprSet` (merging equal subtrees even when not
  pointer-shared, yielding only the first occurrence's `ExprContext`). Set `false` to emit every
  occurrence with its own `ExprContext`.
  -/
  dedup              : Bool := true
  /--
  Emit intermediate curried `.app` prefixes (`f a₁`, …) inside multi-argument applications;
  when `false` (default), emits full applications and visits head/arguments directly.
  -/
  includeAppPrefixes : Bool := false

/--
Construct a lazy outermost-first stream of closed subterms of `e`, paired with `ExprContext`.
With `dedup := true` (default), structurally equal subterms are deduplicated via `ExprSet` (yielding
only the first occurrence's `ExprContext`); with `dedup := false`, every occurrence is emitted with
its own `ExprContext`. With `includeAppPrefixes := false` (default), intermediate curried
application prefixes are omitted while head and argument `ExprContext` chains stay complete.
-/
def subterms (e : Expr) (dedup : Bool := true) (includeAppPrefixes : Bool := false) : Subterms :=
  { expr := e, dedup, includeAppPrefixes }

mutual
  private def subtermsVisitSpine [Monad m] (dedup : Bool)
      (f : Expr × ExprContext → β → m (ForInStep β))
      (p : Expr) (upper : List ExprContextFrame) (acc : β) :
      StateT ExprSet m (ForInStep β) :=
    match p with
    | .app pf pa => do
      match ← subtermsVisitSpine dedup f pf (.appFn p pa :: upper) acc with
      | .done b  => return .done b
      | .yield b => subtermsGo dedup false f pa (.appArg p pf :: upper) b
    | fn => subtermsGo dedup false f fn upper acc
  termination_by (sizeOf p, 2)

  private def subtermsStepChildren [Monad m] (dedup includeAppPrefixes : Bool)
      (f : Expr × ExprContext → β → m (ForInStep β))
      (cur : Expr) (frames : List ExprContextFrame) (curAcc : β) :
      StateT ExprSet m (ForInStep β) :=
    match cur with
    | .app f0 a => do
      if !includeAppPrefixes then
        match ← subtermsVisitSpine dedup f f0 (.appFn cur a :: frames) curAcc with
        | .done b  => return .done b
        | .yield b => subtermsGo dedup includeAppPrefixes f a (.appArg cur f0 :: frames) b
      else
        match ← subtermsGo dedup includeAppPrefixes f f0 (.appFn cur a :: frames) curAcc with
        | .done b  => return .done b
        | .yield b => subtermsGo dedup includeAppPrefixes f a (.appArg cur f0 :: frames) b
    | .lam _ t b _ => do
      match ← subtermsGo dedup includeAppPrefixes f t (.lamType cur b :: frames) curAcc with
      | .done b'  => return .done b'
      | .yield b' => subtermsGo dedup includeAppPrefixes f b (.lamBody cur t :: frames) b'
    | .forallE _ t b _ => do
      match ← subtermsGo dedup includeAppPrefixes f t (.forallType cur b :: frames) curAcc with
      | .done b'  => return .done b'
      | .yield b' => subtermsGo dedup includeAppPrefixes f b (.forallBody cur t :: frames) b'
    | .letE _ t v b nd => do
      match ← subtermsGo dedup includeAppPrefixes f t (.letType cur v b nd :: frames) curAcc with
      | .done b'  => return .done b'
      | .yield b' =>
        match ← subtermsGo dedup includeAppPrefixes f v (.letVal cur t b nd :: frames) b' with
        | .done b''  => return .done b''
        | .yield b'' => subtermsGo dedup includeAppPrefixes f b (.letBody cur t v nd :: frames) b''
    | .proj _ _ b =>
      subtermsGo dedup includeAppPrefixes f b (.proj cur :: frames) curAcc
    | _ => pure (.yield curAcc)
  termination_by (sizeOf cur, 0)

  private def subtermsGo [Monad m] (dedup includeAppPrefixes : Bool)
      (f : Expr × ExprContext → β → m (ForInStep β))
      (cur : Expr) (frames : List ExprContextFrame) (acc : β) :
      StateT ExprSet m (ForInStep β) :=
    match cur with
    | .mdata _ b => subtermsGo dedup includeAppPrefixes f b (.mdata cur :: frames) acc
    | cur => do
      if dedup then
        if (← get).contains cur then
          return .yield acc
        modify (·.insert cur)
      let mut curAcc := acc
      if !cur.hasLooseBVars then
        match ← liftM (f (cur, { frames }) curAcc) with
        | .done b  => return .done b
        | .yield b => curAcc := b
      subtermsStepChildren dedup includeAppPrefixes f cur frames curAcc
  termination_by (sizeOf cur, 1)
end

/-- Iterate over closed `(subterm, ctx)` pairs in `s`. -/
def Subterms.forIn [Monad m] (s : Subterms) (init : β)
    (f : Expr × ExprContext → β → m (ForInStep β)) : m β := do
  let (step, _) ← (subtermsGo s.dedup s.includeAppPrefixes f s.expr [] init).run ({} : ExprSet)
  return match step with
    | .done b | .yield b => b

instance [Monad m] : ForIn m Subterms (Expr × ExprContext) where
  forIn := Subterms.forIn

/-- Collect all yielded `(subterm, ctx)` pairs from `s` into an `Array`. -/
def Subterms.toArray (s : Subterms) : Array (Expr × ExprContext) := Id.run do
  let mut acc : Array (Expr × ExprContext) := #[]
  for item in s do
    acc := acc.push item
  return acc

/-- Collect all yielded `(subterm, ctx)` pairs from `s` into a `List`. -/
def Subterms.toList (s : Subterms) : List (Expr × ExprContext) :=
  s.toArray.toList

/--
Lazy stream of closed `match` (and optionally `casesOn`) discriminants occurring in an `Expr`,
each paired with its `ExprContext`. Created by `matchDiscriminants`. Supports `for` iteration with
early exit (`break`) in any monad lifting `MetaM`, plus `.toArray` and `.toList`.
-/
structure MatchDiscriminants where
  /-- Root expression to traverse. -/
  expr        : Expr
  /-- Also recognize `casesOn` recursor applications in addition to compiled `match` expressions. -/
  alsoCasesOn : Bool := false
  /--
  Deduplicate visited subtrees and structurally equal discriminants via `ExprSet` (merging
  structurally equal subtrees even when not pointer-shared, yielding only the first occurrence's
  `ExprContext`). Set `false` to visit and yield every occurrence with its own `ExprContext`.
  -/
  dedup       : Bool := true

/--
Construct a lazy outermost-first stream of closed `match` (and optionally `casesOn`) discriminants
occurring in `e`, paired with `ExprContext`.
With `dedup := true` (default), structurally equal subtrees and discriminants are deduplicated via
`ExprSet` (yielding only the first occurrence's `ExprContext`); with `dedup := false`, every
occurrence is emitted with its own `ExprContext`.
-/
def matchDiscriminants (e : Expr) (alsoCasesOn : Bool := false) (dedup : Bool := true) :
    MatchDiscriminants :=
  { expr := e, alsoCasesOn, dedup }

private def collectAppSpineArgsSub (n : Nat) (cur : Expr) (upper : List ExprContextFrame) :
    List ({ e : Expr // sizeOf e < sizeOf cur } × List ExprContextFrame) :=
  go n cur upper (Nat.le_refl _) []
where
  go : (k : Nat) → (p : Expr) → List ExprContextFrame → sizeOf p ≤ sizeOf cur →
      List ({ e : Expr // sizeOf e < sizeOf cur } × List ExprContextFrame) →
      List ({ e : Expr // sizeOf e < sizeOf cur } × List ExprContextFrame)
    | k + 1, p@(.app pf pa), upper, hp, acc =>
      have hpa : sizeOf pa < sizeOf cur := by
        have hlt : sizeOf pa < sizeOf (Expr.app pf pa) := by decreasing_tactic
        exact Nat.lt_of_lt_of_le hlt hp
      have hpf : sizeOf pf ≤ sizeOf cur := by
        have hlt : sizeOf pf < sizeOf (Expr.app pf pa) := by decreasing_tactic
        exact Nat.le_of_lt (Nat.lt_of_lt_of_le hlt hp)
      go k pf (.appFn p pa :: upper) hpf ((⟨pa, hpa⟩, .appArg p pf :: upper) :: acc)
    | _, _, _, _, acc => acc

mutual
  private def matchDiscriminantsGoArgs [Monad m] [MonadLiftT MetaM m] {β : Type}
      (alsoCasesOn dedup : Bool) (f : Expr × ExprContext → β → m (ForInStep β))
      (parent : Expr)
      (entries : List ({ e : Expr // sizeOf e < sizeOf parent } × List ExprContextFrame))
      (acc : β) : StateT (ExprSet × ExprSet) m (ForInStep β) := do
    match entries with
    | [] => return .yield acc
    | (⟨arg, _⟩, argFrames) :: rest =>
      match ← matchDiscriminantsGo alsoCasesOn dedup f arg argFrames acc with
      | .done b  => return .done b
      | .yield b => matchDiscriminantsGoArgs alsoCasesOn dedup f parent rest b
  termination_by (sizeOf parent, 1, entries.length)

  private def matchDiscriminantsStepChildren [Monad m] [MonadLiftT MetaM m] {β : Type}
      (alsoCasesOn dedup : Bool) (f : Expr × ExprContext → β → m (ForInStep β))
      (cur : Expr) (frames : List ExprContextFrame) (acc : β) :
      StateT (ExprSet × ExprSet) m (ForInStep β) :=
    match cur with
    | .app f0 a => do
      match ← matchDiscriminantsGo alsoCasesOn dedup f f0 (.appFn cur a :: frames) acc with
      | .done b  => return .done b
      | .yield b => matchDiscriminantsGo alsoCasesOn dedup f a (.appArg cur f0 :: frames) b
    | .lam _ t b _ => do
      match ← matchDiscriminantsGo alsoCasesOn dedup f t (.lamType cur b :: frames) acc with
      | .done b'  => return .done b'
      | .yield b' => matchDiscriminantsGo alsoCasesOn dedup f b (.lamBody cur t :: frames) b'
    | .forallE _ t b _ => do
      match ← matchDiscriminantsGo alsoCasesOn dedup f t (.forallType cur b :: frames) acc with
      | .done b'  => return .done b'
      | .yield b' => matchDiscriminantsGo alsoCasesOn dedup f b (.forallBody cur t :: frames) b'
    | .letE _ t v b nd => do
      match ← matchDiscriminantsGo alsoCasesOn dedup f t (.letType cur v b nd :: frames) acc with
      | .done b'  => return .done b'
      | .yield b' =>
        match ← matchDiscriminantsGo alsoCasesOn dedup f v (.letVal cur t b nd :: frames) b' with
        | .done b''  => return .done b''
        | .yield b'' =>
          matchDiscriminantsGo alsoCasesOn dedup f b (.letBody cur t v nd :: frames) b''
    | .proj _ _ b =>
      matchDiscriminantsGo alsoCasesOn dedup f b (.proj cur :: frames) acc
    | _ => pure (.yield acc)
  termination_by (sizeOf cur, 0, 0)

  private def matchDiscriminantsGo [Monad m] [MonadLiftT MetaM m] {β : Type}
      (alsoCasesOn dedup : Bool) (f : Expr × ExprContext → β → m (ForInStep β))
      (cur : Expr) (frames : List ExprContextFrame) (acc : β) :
      StateT (ExprSet × ExprSet) m (ForInStep β) :=
    match cur with
    | .mdata _ b =>
      matchDiscriminantsGo alsoCasesOn dedup f b (.mdata cur :: frames) acc
    | cur => do
      if dedup then
        if (← get).1.contains cur then
          return .yield acc
        modify fun (vis, em) => (vis.insert cur, em)
      if cur.isApp && cur.getAppFn.isConst then
        if let some app ← liftM (matchMatcherApp? cur alsoCasesOn : MetaM (Option MatcherApp)) then
          let argEntries := collectAppSpineArgsSub cur.getAppNumArgs cur frames
          let discrStart := app.params.size + 1
          let discrEnd := discrStart + app.discrs.size
          let mut curAcc := acc
          let mut idx := 0
          for (⟨arg, _⟩, argFrames) in argEntries do
            if idx >= discrStart && idx < discrEnd && !arg.hasLooseBVars then
              let shouldEmit ←
                if dedup then
                  let em := (← get).2
                  if em.contains arg then
                    pure false
                  else
                    modify fun (vis, em) => (vis, em.insert arg)
                    pure true
                else
                  pure true
              if shouldEmit then
                match ← liftM (f (arg, { frames := argFrames }) curAcc) with
                | .done b  => return .done b
                | .yield b => curAcc := b
            idx := idx + 1
          return ← matchDiscriminantsGoArgs alsoCasesOn dedup f cur argEntries curAcc
      matchDiscriminantsStepChildren alsoCasesOn dedup f cur frames acc
  termination_by (sizeOf cur, 2, 0)
end

/-- Iterate over closed `(discr, ctx)` pairs in `d`. -/
def MatchDiscriminants.forIn [Monad m] [MonadLiftT MetaM m] (d : MatchDiscriminants) (init : β)
    (f : Expr × ExprContext → β → m (ForInStep β)) : m β := do
  let e ← (instantiateMVarsIfNeeded d.expr : MetaM Expr)
  let (step, _) ← (matchDiscriminantsGo d.alsoCasesOn d.dedup f e [] init).run
    (({} : ExprSet), ({} : ExprSet))
  return match step with
    | .done b | .yield b => b

instance [Monad m] [MonadLiftT MetaM m] : ForIn m MatchDiscriminants (Expr × ExprContext) where
  forIn := MatchDiscriminants.forIn

/-- Collect all yielded `(discr, ctx)` pairs from `d` into an `Array`. -/
def MatchDiscriminants.toArray (d : MatchDiscriminants) : MetaM (Array (Expr × ExprContext)) := do
  let mut acc : Array (Expr × ExprContext) := #[]
  for item in d do
    acc := acc.push item
  return acc

/-- Collect all yielded `(discr, ctx)` pairs from `d` into a `List`. -/
def MatchDiscriminants.toList (d : MatchDiscriminants) : MetaM (List (Expr × ExprContext)) :=
  (·.toList) <$> d.toArray

end Lean.Meta
