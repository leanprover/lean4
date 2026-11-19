import Lean

/-!
This benchmark exercises `instantiateMVars` on chains of hypotheses introduced
via `MVarId.assert`+`intro` (as done by `MVarId.note`, `replaceLocalDecl`,
`simp at h`, ...) whose proofs reference the previous hypothesis several times,
from different binder depths and from inside lambdas. Resolving the delayed
assignments substitutes these hypothesis proofs into their use sites, lifted
to the respective binder depth, and the lifted copies must be shared for the
instantiated proof term to stay small (issue #14329).

Each step destructures an existential (adding binder depth) and notes a new
hypothesis whose proof references the previous one three times.
-/

set_option maxHeartbeats 40000000

axiom S : Type
axiom Rel : S → S → Prop
axiom s0 : S
axiom rel0 : Rel s0 s0
axiom ex : ∀ (s : S), ∃ t, Rel s t
axiom comb : ∀ {a b : S}, (S → Rel a b) → (S → S → Rel a b) → Rel a b → Rel a b

open Lean Meta

-- n=1000 is calibrated to take roughly 1s total elaboration time.
-- Use a small n unless TEST_BENCH=1, so that the test suite runs quickly.
run_meta do
  let bench := (← IO.getEnv "TEST_BENCH") == some "1"
  let n := if bench then 1000 else 15
  let g0 ← mkFreshExprSyntheticOpaqueMVar (mkConst ``True)
  let mut g := g0.mvarId!
  let mut t : Expr := mkConst ``s0
  let mut h : Expr := mkConst ``rel0
  for _ in [0:n] do
    let (hexFVar, g') ← g.note `hex (mkApp (mkConst ``ex) t)
    let #[sub] ← g'.cases hexFVar | failure
    g := sub.mvarId
    t := sub.fields[0]!
    let val ← g.withContext do
      let lam1 := mkLambda `x .default (mkConst ``S) h
      let lam2 := mkLambda `x .default (mkConst ``S) (mkLambda `y .default (mkConst ``S) h)
      mkAppM ``comb #[lam1, lam2, h]
    let (hFVar, g'') ← g.note `h val
    g := g''
    h := mkFVar hFVar
  g.assign (mkConst ``True.intro)
  discard <| instantiateMVars g0
