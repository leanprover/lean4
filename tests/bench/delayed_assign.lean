import Lean

open Lean Meta

def mkLE (i : Nat) : Expr :=
  mkNatLE (mkNatLit 0) (mkBVar i)

partial def solve (mvarId : MVarId) : MetaM Unit := do
  let type ← instantiateMVars (← mvarId.getType)
  if type.isForall then
    let (_, mvarId) ← mvarId.intro1
    solve mvarId
  else if type.isAppOf ``And then
    let [mvarId₁, mvarId₂] ← mvarId.applyConst ``And.intro | failure
    solve mvarId₁
    solve mvarId₂
  else if type.isAppOf ``LE.le then
    let [] ← mvarId.applyConst ``Nat.zero_le | failure
  else
    let [] ← mvarId.applyConst ``True.intro | failure

/-! ## instantiateMVarsNoUpdate2: bvar-blind cache variant

Experimental variant of `instantiateMVarsNoUpdate` that keeps its cache across binder depths
using bvar-blind keying: expressions are hashed and compared while treating all `.bvar` indices
as equal. When a cache hit is found at a different depth, we verify the stored key shifted by the
depth difference equals the current expression, then lift the cached result accordingly.

### Analysis

This trades constant per-node overhead (BVarBlindKey allocation, double cache lookup for the
shouldInsert check, richer cache entries) for better depth scaling: the old approach clears the
cache at each binder depth, giving O(depth * bodySize) when the same closed sub-expression
appears at many depths. This variant caches it once and reuses, giving O(bodySize + depth).

Benchmark results (bench2, body=500):

| depth | instantiateMVars | NoUpdate (old) | NoUpdate2 (new) |
|-------|-----------------|----------------|-----------------|
|     1 |         0.15 ms |        0.52 ms |         7.2 ms  |
|    10 |         0.12 ms |        1.80 ms |         5.8 ms  |
|    50 |         0.11 ms |        8.39 ms |         5.9 ms  |
|   100 |         0.12 ms |       17.63 ms |         6.3 ms  |
|   500 |         0.18 ms |      103.23 ms |         7.8 ms  |

On the bench1 workload (delayed assignments from tactics, the realistic case), NoUpdate2 is
3-5x slower than NoUpdate, and both are already sub-millisecond. The ~6ms constant overhead makes
NoUpdate2 worse for shallow depths (crossover ~depth=50). The optimization only pays off for
pathological cases with many nested binders and large shared closed sub-expressions.

**Conclusion:** Not worth adopting as a replacement for the current cache-clearing approach.
-/

namespace InstMVarsNU2

structure DelayedLift where
  originalDepth : Nat
  expr : Expr

private partial def bvarBlindEq (e₁ e₂ : Expr) : Bool :=
  if e₁.looseBVarRange == 0 && e₂.looseBVarRange == 0 then Expr.equal e₁ e₂
  else match e₁, e₂ with
  | .bvar _, .bvar _                         => true
  | .app f₁ a₁, .app f₂ a₂                  => bvarBlindEq f₁ f₂ && bvarBlindEq a₁ a₂
  | .forallE _ d₁ b₁ bi₁, .forallE _ d₂ b₂ bi₂ =>
      bi₁ == bi₂ && bvarBlindEq d₁ d₂ && bvarBlindEq b₁ b₂
  | .lam _ d₁ b₁ bi₁, .lam _ d₂ b₂ bi₂     =>
      bi₁ == bi₂ && bvarBlindEq d₁ d₂ && bvarBlindEq b₁ b₂
  | .letE _ t₁ v₁ b₁ nd₁, .letE _ t₂ v₂ b₂ nd₂ =>
      nd₁ == nd₂ && bvarBlindEq t₁ t₂ && bvarBlindEq v₁ v₂ && bvarBlindEq b₁ b₂
  | .mdata d₁ b₁, .mdata d₂ b₂              => d₁ == d₂ && bvarBlindEq b₁ b₂
  | .proj n₁ i₁ b₁, .proj n₂ i₂ b₂          => n₁ == n₂ && i₁ == i₂ && bvarBlindEq b₁ b₂
  | _, _                                      => false

structure BVarBlindKey where
  expr : Expr
  bbHash : UInt64

instance : Hashable BVarBlindKey where
  hash k := k.bbHash

instance : BEq BVarBlindKey where
  beq k₁ k₂ := k₁.bbHash == k₂.bbHash && bvarBlindEq k₁.expr k₂.expr

structure CacheEntry where
  depth : Nat
  key : Expr
  result : Expr

structure Context where
  depth : Nat := 0
  fvarSubst : PersistentHashMap FVarId DelayedLift := {}

structure State where
  cache : Std.HashMap BVarBlindKey CacheEntry := {}

abbrev M := ReaderT Context (StateRefT State MetaM)

/-- Compute bvar-blind hash. For closed sub-expressions, uses precomputed hash. -/
private def bbHash (e : Expr) : UInt64 :=
  -- For this benchmark, all cross-depth expressions are closed, so just use regular hash.
  -- A full implementation would ignore bvar indices.
  e.hash

def withLift (n : Nat) (k : M α) : M α :=
  withTheReader Context (fun ctx =>
    { ctx with depth := ctx.depth + n }) k

def withSubst (fvarIds : Array Expr) (args : Array Expr) : M α → M α :=
  withTheReader Context fun ctx => Id.run do
    let mut mvarSubst := ctx.fvarSubst
    for fvarId in fvarIds, arg in args do
      mvarSubst := mvarSubst.erase fvarId.fvarId! |>.insert fvarId.fvarId! ⟨ctx.depth, arg⟩
    { ctx with fvarSubst := mvarSubst }

def lookup? (fvarId : FVarId) : M (Option Expr) := do
  let ctx ← read
  match ctx.fvarSubst.find? fvarId with
  | some ds => return ds.expr.liftLooseBVars (s := 0) (d := ctx.depth - ds.originalDepth)
  | none => return none

partial def go (e : Expr) : M Expr := do
  unless e.hasMVar || e.hasFVar do
    return e

  let depth := (← read).depth
  let key := BVarBlindKey.mk e (bbHash e)
  if let some entry := (← get).cache[key]? then
    if entry.depth ≤ depth then
      let k := depth - entry.depth
      let rangeOk := if entry.key.looseBVarRange == 0 then
          e.looseBVarRange == 0
        else
          e.looseBVarRange == entry.key.looseBVarRange + k
      if rangeOk then
        if k == 0 then
          if Expr.equal entry.key e then return entry.result
        else
          if entry.key.liftLooseBVars 0 k == e then
            return entry.result.liftLooseBVars 0 k

  let goApp (e : Expr) := e.withApp fun f args => do
    let args ← args.mapM go
    let instArgs (f' : Expr) : M Expr := do
      pure (mkAppN f' args)
    let instApp : M Expr := do
      let wasMVar := f.isMVar
      let f' ← go f
      if wasMVar && f'.isLambda then
        go (f'.betaRev args.reverse (useZeta := true))
      else
        instArgs f'
    if let .mvar mvarId := f then
      let some {fvars, mvarIdPending} ← getDelayedMVarAssignment? mvarId | return ← instApp
      if fvars.size > args.size then
        return ← instArgs f
      let substArgs := args[:fvars.size].copy
      let extraArgs := args[fvars.size:].copy
      let newVal ← withSubst fvars substArgs <|
        go (mkMVar mvarIdPending)
      let result := mkAppN newVal extraArgs
      return result
    instApp

  let e' ← match e with
    | .bvar .. | .lit ..  => unreachable!
    | .proj _ _ s      => return e.updateProj! (← go s)
    | .forallE _ d b _ => return e.updateForallE! (← go d) (← withLift 1 <| go b)
    | .lam _ d b _     => return e.updateLambdaE! (← go d) (← withLift 1 <| go b)
    | .letE _ t v b nd => return e.updateLet! (← go t) (← go v) (← withLift 1 <| go b) nd
    | .const _ lvls    => return e.updateConst! (← lvls.mapM (instantiateLevelMVars ·))
    | .sort lvl        => return e.updateSort! (← instantiateLevelMVars lvl)
    | .mdata _ b       => return e.updateMData! (← go b)
    | .fvar fvarId     => return (← lookup? fvarId).getD e
    | .app ..          => goApp e
    | .mvar mvarId     =>
        match (← getExprMVarAssignment? mvarId) with
        | some newE =>
          let newE ← go newE
          return newE
        | none => pure e
  let shouldInsert := match (← get).cache[key]? with
    | none => true
    | some entry => depth ≤ entry.depth
  if shouldInsert then
    modify fun s => { s with cache := s.cache.insert key ⟨depth, e, e'⟩ }
  return e'

end InstMVarsNU2

def _root_.Lean.Meta.instantiateMVarsNoUpdate2 (e : Expr) : MetaM Expr := do
  (InstMVarsNU2.go e).run {} |>.run' {}

/-! ## Benchmark 1: delayed assignments (from original benchmark) -/

partial def runBench1 (name : String) (n : Nat) (mk : Nat → MetaM MVarId) : MetaM Unit := do
  let mvarId ← mk n
  let startTime ← IO.monoNanosNow
  solve mvarId
  let endTime ← IO.monoNanosNow
  let ms := (endTime - startTime).toFloat / 1000000.0
  let startTime ← IO.monoNanosNow
  discard <| instantiateMVars (mkMVar mvarId)
  let endTime ← IO.monoNanosNow
  let instMs := (endTime - startTime).toFloat / 1000000.0
  IO.println s!"{name}_{n}: {ms} ms, instantiateMVars: {instMs} ms"

def mkBench1 (n : Nat) : MetaM MVarId := do
  let type := mkType n
  return (← mkFreshExprSyntheticOpaqueMVar type).mvarId!
where
  mkResultType (i : Nat) : Expr :=
    match i with
    | 0 => mkConst ``True
    | i+1 => mkAnd (mkLE i) (mkResultType i)

  mkType (i : Nat) : Expr :=
    match i with
    | 0 => mkResultType n
    | i+1 => .forallE `x Nat.mkType (mkAnd (mkType i) (mkLE (n - i - 1))) .default

partial def bench1 (n : Nat) : MetaM Unit := do
  runBench1 "bench1" n mkBench1

/-! ## Benchmark 2: shared closed sub-expression across binder depths

A closed sub-expression containing mvars appears as the domain of nested foralls.
The old NoUpdate clears its cache at each depth, recomputing the sub-expression each time.
The new NoUpdate2 caches it once and reuses across depths.

Structure: `∀ _ : bigExpr, ∀ _ : bigExpr, ... bigExpr`
where `bigExpr = (?m₁ ≤ 1) ∧ (?m₂ ≤ 1) ∧ ... ∧ True` with each `?mᵢ := 0`.
-/

/-- Create a conjunction of `size` mvar lookups. -/
def mkMVarConj (size : Nat) : MetaM Expr := do
  let mut expr := mkConst ``True
  for _ in [:size] do
    let mvar ← mkFreshExprMVar (mkConst ``Nat)
    mvar.mvarId!.assign (mkNatLit 0)
    expr := mkAnd (mkNatLE mvar (mkNatLit 1)) expr
  return expr

/-- Nest `bigExpr` under `depth` forall binders (also used as each domain). -/
def mkNestedForall (bigExpr : Expr) (depth : Nat) : Expr := Id.run do
  let mut term := bigExpr
  for _ in [:depth] do
    term := .forallE `x bigExpr term .default
  return term

def bench2 (depth : Nat) (bodySize : Nat) : MetaM Unit := do
  -- Each test gets fresh mvars to avoid cross-contamination from instantiateMVars updating assignments
  let bigExpr1 ← mkMVarConj bodySize
  let term1 := mkNestedForall bigExpr1 depth
  let t0 ← IO.monoNanosNow
  let _r1 ← instantiateMVarsNoUpdate term1
  let t1 ← IO.monoNanosNow

  let bigExpr2 ← mkMVarConj bodySize
  let term2 := mkNestedForall bigExpr2 depth
  let t2 ← IO.monoNanosNow
  let _r2 ← instantiateMVarsNoUpdate2 term2
  let t3 ← IO.monoNanosNow

  let bigExpr3 ← mkMVarConj bodySize
  let term3 := mkNestedForall bigExpr3 depth
  let t4 ← IO.monoNanosNow
  let _r3 ← instantiateMVars term3
  let t5 ← IO.monoNanosNow

  let nuMs := (t1 - t0).toFloat / 1000000.0
  let nu2Ms := (t3 - t2).toFloat / 1000000.0
  let instMs := (t5 - t4).toFloat / 1000000.0

  IO.println s!"bench2 depth={depth} body={bodySize}: instantiateMVars {instMs} ms, NoUpdate {nuMs} ms, NoUpdate2 {nu2Ms} ms"

/-! ## Run benchmarks -/

run_meta do
  IO.println "=== Bench 1: delayed assignments ==="
  for i in [10, 20, 40, 80, 100, 200, 300, 400, 500] do
    bench1 i

  IO.println ""
  IO.println "=== Bench 2: shared closed sub-expr across depths (body=500, varying depth) ==="
  for d in [1, 10, 50, 100, 200, 500] do
    bench2 d 500

  IO.println ""
  IO.println "=== Bench 2: shared closed sub-expr across depths (depth=100, varying body) ==="
  for b in [100, 500, 1000, 2000] do
    bench2 100 b
