import Lean

/-!
`isDefEqProjInst` must report a failed comparison as `.false`, not `.undef`.

It decides `k =?= C.op instA ?m` by unfolding the instance projection and running a full
comparison on the result. Reporting `.false` short-circuits the remaining heuristics in
`isExprDefEqExpensive`. Were it to report `.undef` instead — as a "soft" variant that declines
whenever either side contains a metavariable would — `isDefEqOnFailure` would run again on the
original, un-unfolded pair, redoing stuck-metavariable synthesis and unification-hint lookups
for a comparison that has already been decided. That cost compounds: the enclosing comparison is
retried at every unfolding stage, so it grows with the nesting depth of the projections.

That variant was measured against Mathlib: `RingTheory/Regular/RegularSequence.lean` went from
8159 to 98939 `isDefEqOnFailure` invocations (12x) and stopped compiling, exhausting the
heartbeat budget around `IsWeaklyRegular.prototype_perm` — still timing out at 20x the default
limit.

This test pins that cost rather than a particular implementation. `k` is opaque, so none of the
200 comparisons below can succeed; the only question is how much work is spent failing. Cost is
linear in the iteration count with no measurable fixed overhead, so the margins are set by the
depth: the budget is roughly 3x what the `.false` version needs, while the declining variant needs
about 12x. It therefore fails here with a deterministic timeout instead of a silent slowdown.
-/

open Lean Meta

class C (α : Type) where
  op : α → α

instance instA : C Nat := ⟨fun n => n + 1⟩

opaque k : Nat

/-- `C.op instA (C.op instA (... e))`, `depth` applications deep. -/
def nest : Nat → Expr → Expr
  | 0,   e => e
  | n+1, e => mkApp3 (mkConst ``C.op) (mkConst ``Nat) (mkConst ``instA) (nest n e)

def tst (depth iters : Nat) : MetaM Unit :=
  withTransparency .instances do
    for _ in [0:iters] do
      let m ← mkFreshExprMVar (mkConst ``Nat)
      discard <| isDefEq (mkConst ``k) (nest depth m)

set_option maxHeartbeats 1200 in
run_meta tst 400 200
