import Lean

/-!
This test ensures that nested instance projections are efficiently handled by `isDefEq`.

Context: In an earlier version of Lean, `isDefEqOnFailure` was sometimes called twice, once before
and once after `isDefEqProjInst`, if `isDefEqProjInst` returned `.undef`. For nexted instance
projections, this blew up the amount of heartbeats needed.

That problem was observed in Mathlib: `RingTheory/Regular/RegularSequence.lean` went from
8159 to 98939 `isDefEqOnFailure` invocations and exhausted the heartbeat limit around
`IsWeaklyRegular.prototype_perm`.

The heartbeat limit is 3x as much as is needed as of writing, so that the test is robust against
fluctuations.
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

set_option maxHeartbeats 1300 in
run_meta tst 400 200
