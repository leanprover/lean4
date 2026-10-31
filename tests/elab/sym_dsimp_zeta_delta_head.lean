import Lean

/-!
Tests that `Sym.DSimp.zetaDelta`/`zetaDeltaAll` unfold a let-bound free variable that
appears in the head position of an application. `Sym.dsimp` does not visit application
heads, so the simproc has to match on the whole application. This test uses the
programmatic API with `pre := zetaDeltaAll >> beta`, mirroring `bv_decide`'s
normalization passes.
-/

open Lean Meta Elab Tactic Sym Sym.DSimp

elab "dsimp_zeta_delta_all" : tactic => do
  let g ← getMainGoal
  let g ← SymM.run do
    let g ← Sym.preprocessMVar g
    g.withContext do
      let type ← g.getType
      let methods : Methods := { pre := zetaDeltaAll >> beta }
      let res ← Sym.dsimp type (methods := methods)
      logInfo m!"result: {res}"
      return g
  setGoals [g]

/-- info: result: a + b = b + a -/
#guard_msgs in
example (a b : BitVec 32) :
    let foo := fun (x y : BitVec 32) => x + y;
    foo a b = foo b a := by
  intro foo
  dsimp_zeta_delta_all
  exact BitVec.add_comm a b

-- `zetaDeltaAll` alone exposes the lambda; `beta` is a separate step.
elab "dsimp_zeta_delta_all_no_beta" : tactic => do
  let g ← getMainGoal
  let g ← SymM.run do
    let g ← Sym.preprocessMVar g
    g.withContext do
      let type ← g.getType
      let methods : Methods := { pre := zetaDeltaAll }
      let res ← Sym.dsimp type (methods := methods)
      logInfo m!"result: {res}"
      return g
  setGoals [g]

/-- info: result: (fun x y => x + y) a b = (fun x y => x + y) b a -/
#guard_msgs in
example (a b : BitVec 32) :
    let foo := fun (x y : BitVec 32) => x + y;
    foo a b = foo b a := by
  intro foo
  dsimp_zeta_delta_all_no_beta
  exact BitVec.add_comm a b

-- A variable without a value in head position is left alone.
/-- info: result: f a b = f b a -/
#guard_msgs in
example (a b : BitVec 32) (f : BitVec 32 → BitVec 32 → BitVec 32) (h : f a b = f b a) :
    f a b = f b a := by
  dsimp_zeta_delta_all
  exact h
