import Lean

/-!
Regression tests for `expr` quotations (`core_spec_v1.md` §7):
- Distinct anonymous hypotheses (`_ : ?A, _ : ?B`) and multiple wildcards `_` never conflate
  distinct hypotheses or distinct subterms.
- Commit vs fall-through: failed alternatives never leak partial pattern matches, `MCtx`
  assignments, `Sym` temporary mvars, or RHS side effects into later alternatives or callers.
- Stale-context checks: mutating local declarations, clearing `fvar`s, or switching goals across
  iterations never reads stale context values or corrupts `ExprContext.fill`.
-/

namespace ExprQuotRegressionsTest

open Lean Meta
open Lean.Meta.Sym (SymM)

opaque rTag : Nat → Nat → Nat
opaque pTag : Nat → Prop

/-! ## 1. Distinct anonymous hypotheses & non-conflating wildcards -/

private def matchWildcardArgs (e : Expr) : MetaM (Option (Expr × Expr)) :=
  match e with
  | `(expr| rTag _ _) => return some (e.appFn!.appArg!, e.appArg!)
  | _                 => return none

private def collectMatchingHyps : MetaM (Array (Name × Expr)) := do
  let mut out := #[]
  for case (_, `(expr| pTag ?a)) in (← localHypTypes) do
    out := out.push (`hit, a)
  return out

/-- info: (true, true, 3) -/
#guard_msgs in
run_meta do
  -- Multiple `_` wildcards inside `rTag _ _` never unify distinct arguments
  let diff ← `(expr| rTag 1 2)
  let hitDiff ← matchWildcardArgs diff
  let okWildcard := hitDiff.any fun (a, b) => a == mkNatLit 1 && b == mkNatLit 2

  -- Non-named `_` wildcards in mixed named+wildcard pattern never force equality
  let twoWildcard : Expr → MetaM Bool
    | `(expr| rTag _ ?x) => let _ := x; return true
    | _                  => return false
  let okMixed ← twoWildcard (← `(expr| rTag 7 8))

  -- Distinct anonymous `_` hypotheses in the local context remain distinct in `localHypTypes`
  let anonHits ←
    withLocalDeclD `_ (mkApp (mkConst ``pTag) (mkNatLit 10)) fun _ =>
    withLocalDeclD `_ (mkConst ``Nat) fun _ =>
    withLocalDeclD `_ (mkApp (mkConst ``pTag) (mkNatLit 20)) fun _ =>
    withLocalDeclD `H (mkApp (mkConst ``pTag) (mkNatLit 30)) fun _ =>
      collectMatchingHyps
  let matchedArgs ←
    withLocalDeclD `_ (mkApp (mkConst ``pTag) (mkNatLit 10)) fun _ =>
    withLocalDeclD `_ (mkConst ``Nat) fun _ =>
    withLocalDeclD `_ (mkApp (mkConst ``pTag) (mkNatLit 20)) fun _ =>
    withLocalDeclD `H (mkApp (mkConst ``pTag) (mkNatLit 30)) fun _ => do
      let mut vals : Array Expr := #[]
      for case (_, `(expr| pTag ?n)) in (← localHypTypes) do
        vals := vals.push n
      return vals
  let expected := #[mkNatLit 10, mkNatLit 20, mkNatLit 30]
  let okOrder := anonHits.size == 3 && matchedArgs == expected
  let hitCount : Nat := if okOrder then 3 else 0
  logInfo m!"({okWildcard}, {okMixed}, {hitCount})"

/-! ## 2. Commit vs fall-through: zero side-effect / MCtx leakage -/

private def nonLinearCommitTest (e : Expr) (logRef : IO.Ref (Array String)) : MetaM Nat :=
  match e with
  | `(expr/reducible| ?a + $a) => do
    logRef.modify (·.push "arm1")
    let _ := a
    return 1
  | `(expr/reducible| ?a + ?b) => do
    logRef.modify (·.push "arm2")
    let _ := (a, b)
    return 2
  | _ => do
    logRef.modify (·.push "fallback")
    return 0

private def symCommitTest (e : Expr) (pinVal : Expr) (logRef : IO.Ref (Array String)) :
    SymM Nat :=
  match e with
  | `(expr/sym| $pinVal + ?y) => do
    logRef.modify (·.push "symArm1")
    let _ := y
    return 1
  | `(expr/sym| ?x + ?y) => do
    logRef.modify (·.push "symArm2")
    let _ := (x, y)
    return 2
  | _ => do
    logRef.modify (·.push "symFallback")
    return 0

/-- info: (2, [arm2], true, 2, [symArm2], true) -/
#guard_msgs in
run_meta do
  let logRef ← IO.mkRef #[]
  let mv ← mkFreshExprMVar (some (mkConst ``Nat))
  let t1 ← `(expr| $mv + (5 : Nat))
  let r1 ← nonLinearCommitTest t1 logRef
  -- Failed `arm1` (`?a + $a`) MUST NOT assign `mv := 5` into `MCtx` before committing `arm2`!
  let mvStillFree := !(← mv.mvarId!.isAssigned)
  let log1 ← logRef.get

  let symLogRef ← IO.mkRef #[]
  let pin4 ← `(expr| (4 : Nat))
  let (symRes, symFree) ← SymM.run do
    let mvSym ← mkFreshExprMVar (some (mkConst ``Nat))
    let tSym ← `(expr| $mvSym + (9 : Nat))
    let r ← symCommitTest tSym pin4 symLogRef
    let symAssigned ← mvSym.mvarId!.isAssigned
    return (r, !symAssigned)
  let symLog ← symLogRef.get
  logInfo m!"({r1}, {log1.toList}, {mvStillFree}, {symRes}, {symLog.toList}, {symFree})"

-- Commit inside `do` `if let` / `let ... |` control flow without fallback leak
private def doCommitControlFlow (e : Expr) (trace : IO.Ref (Array String)) : MetaM Nat := do
  if let `(expr| ?x + $x) := e then
    trace.modify (·.push "ifLet")
    let _ := x
    return 10
  let `(expr| ?a + ?b) := e
    | do
      trace.modify (·.push "elseLet")
      return 0
  trace.modify (·.push "committed")
  let _ := (a, b)
  return 20

/-- info: (20, [committed]) -/
#guard_msgs in
run_meta do
  let ref ← IO.mkRef #[]
  let r ← doCommitControlFlow (← `(expr| 1 + 2)) ref
  logInfo m!"({r}, {(← ref.get).toList})"

/-! ## 3. Stale-context checks across goal / LCtx mutations -/

/-- info: (true, true, true) -/
#guard_msgs in
run_meta do
  -- 3a. Mutating local `let` bindings across invocations of the same call site must not read stale
  -- cached local `$x` unfoldings.
  let runAtLet (v : Nat) : MetaM Bool :=
    withLetDecl `k (mkConst ``Nat) (mkNatLit v) fun kVar => do
      match ← `(expr| $kVar + (1 : Nat)) with
      | `(expr [+ $kVar]| (5 : Nat) + (1 : Nat)) => return true
      | _                                        => return false
  let resA ← runAtLet 5
  let resB ← runAtLet 6
  let okLocalItem := resA && !resB

  -- 3b. Clearing an `fvar` in a goal (`MVarId.clear`) drops it from subsequent `localHypTypes`
  let okClearedGoal ← withLocalDeclD `h1 (mkApp (mkConst ``pTag) (mkNatLit 1)) fun h1 =>
    withLocalDeclD `h2 (mkApp (mkConst ``pTag) (mkNatLit 2)) fun h2 => do
      let g ← mkFreshExprSyntheticOpaqueMVar (mkConst ``True)
      let gCleared ← g.mvarId!.clear h1.fvarId!
      gCleared.withContext do
        let mut seen : Array Expr := #[]
        for case (_, `(expr| pTag ?n)) in (← localHypTypes) do
          seen := seen.push n
        let stillHasH2 := (← localHypDecls).any (·.1 == h2)
        return seen == #[mkNatLit 2] && stillHasH2

  -- 3c. Goal switching across states updates `ExprContext.fill` against the live target
  let target1 ← `(expr| ((1 : Nat) + (2 : Nat)) + (3 : Nat))
  let target2 ← `(expr| ((4 : Nat) + (5 : Nat)) + (6 : Nat))
  let g1 ← mkFreshExprMVar target1
  let g2 ← mkFreshExprMVar target2
  let rewriteSub (g : Expr) : MetaM (Option Expr) := g.mvarId!.withContext do
    for (sub, ctx) in subterms (← g.mvarId!.getType) do
      if let `(expr| (1 : Nat) + (2 : Nat)) := sub then
        return some (ctx.fill (← `(expr| (99 : Nat))))
      if let `(expr| (4 : Nat) + (5 : Nat)) := sub then
        return some (ctx.fill (← `(expr| (88 : Nat))))
    return none
  let filled1 ← rewriteSub g1
  let filled2 ← rewriteSub g2
  let okGoals := filled1 == some (← `(expr| (99 : Nat) + (3 : Nat))) &&
    filled2 == some (← `(expr| (88 : Nat) + (6 : Nat)))
  logInfo m!"({okLocalItem}, {okClearedGoal}, {okGoals})"

end ExprQuotRegressionsTest