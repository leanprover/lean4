import Std.Tactic.BVDecide
import Lean

/-!
Measures incremental `bv_decide` processing inside `sym =>`.

A chain of `n` preconditions is asserted as hypotheses, optionally normalized with a single
`bv_decide_push`, and then `k` independent queries are forked off the same `Grind.Goal` and
discharged with `bv_decide`. Only the time spent in the forked queries is reported, so the
measurement isolates how much of the shared state each query has to reprocess.

Every link of the chain is a large term that the `bv_normalize` pipeline collapses back to the
previous link by rewriting alone (constant folding of `+`/`-`, all-ones masking, `||| 0`), so
the problem is dominated by rewriting big terms rather than by bit-blasting and SAT solving.
-/

namespace BVDecideIncremental

open Lean Meta

opaque st : Nat → BitVec 64

set_option maxHeartbeats 0
set_option maxRecDepth 0

private structure Ops where
  add : Expr
  sub : Expr
  and : Expr
  or : Expr

private def bvTy : Expr := mkApp (mkConst ``BitVec) (mkNatLit 64)

private def Ops.mk' : MetaM Ops := do
  let inst (cls : Name) : MetaM Expr :=
    synthInstance (mkApp3 (mkConst cls [0, 0, 0]) bvTy bvTy bvTy)
  return { add := ← inst ``HAdd, sub := ← inst ``HSub, and := ← inst ``HAnd, or := ← inst ``HOr }

private def mkBinOp (fn : Name) (inst a b : Expr) : Expr :=
  mkApp6 (mkConst fn [0, 0, 0]) bvTy bvTy bvTy inst a b

private def mkSt (i : Nat) : Expr :=
  mkApp (mkConst ``st) (mkNatLit i)

private def mkBVEq (a b : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [1]) bvTy a b

/--
A term of size `O(m)` that `bv_normalize` collapses back to `e` by rewriting alone:
`m` rounds of `((e + c) - c) &&& <all ones> ||| 0`.
-/
private def mkCollapsing (ops : Ops) (e : Expr) (m : Nat) : Expr := Id.run do
  let allOnes := toExpr 0xffffffffffffffff#64
  let zero := toExpr 0#64
  let m := BitVec.ofNat 64 m
  let mut e := e
  for j in 0...m do
    let c := toExpr <| j + 1
    e := mkBinOp ``HAdd.hAdd ops.add e c
    e := mkBinOp ``HSub.hSub ops.sub e c
    e := mkBinOp ``HAnd.hAnd ops.and e allOnes
    e := mkBinOp ``HOr.hOr ops.or e zero
  return e

open Lean Parser.Tactic.Grind in
syntax (name := bvQueries) "bv_queries" num : grind

open Lean Meta Elab Tactic Grind in
@[grind_tactic bvQueries]
def evalBvQueries : GrindTactic := fun stx => withMainContext do
  let `(grind| bv_queries $numGoals:num) := stx | throwUnsupportedSyntax
  let ops ← Ops.mk'
  let goal ← getMainGoal
  let saved ← getGoals
  let numGoals := numGoals.getNat
  for i in 0...numGoals do
    -- `(st i &&& c) ||| (st i &&& ~~~c) = st i` holds for any value of `st i`, so the query
    -- only measures how much of the surrounding state has to be reprocessed.
    let x := mkSt i
    let prop := mkBVEq
      (mkBinOp ``HOr.hOr ops.or
        (mkBinOp ``HAnd.hAnd ops.and x (toExpr 0xff00#64))
        (mkBinOp ``HAnd.hAnd ops.and x (toExpr 0xffffffffffff00ff#64)))
      x
    let mvar ← mkFreshExprMVar prop
    -- The fresh metavariable inherits the e-graph and the solver states of `goal`.
    setGoals [{ goal with mvarId := mvar.mvarId! }]
    evalGrindTactic (← `(grind| bv_decide -fixedInt -enums -structures (maxSteps := 2000000000)))
  setGoals saved

open Lean Meta Elab Command Term in
def measureTac (tac : TSyntax `tactic) (goal : Expr) : TermElabM Nat := do
  let mvarId := (← mkFreshExprMVar goal).mvarId!
  let startMs ← IO.monoMsNow
  discard <| Tactic.run mvarId (Tactic.evalTactic tac)
  let endMs ← IO.monoMsNow
  return endMs - startMs

open Lean Meta Elab Command Term in
elab "#queries " label:str numHyps:num sizeHyps:num numGoals:num : command => do
  let numHyps := numHyps.getNat
  let sizeHyps := sizeHyps.getNat
  let tacInc ←
      `(tactic| sym -linarith -lia -ac -ring =>
                  intros
                  bv_decide_push (maxSteps := 2000000000000)
                  bv_queries $numGoals
                  all_goals sorry)
  let tacNonInc ←
      `(tactic| sym -linarith -lia -ac -ring =>
                  intros
                  bv_queries $numGoals
                  all_goals sorry)
  liftTermElabM do
    let ops ← Ops.mk'
    let mut goalType := mkBVEq (mkSt 0) (mkSt numHyps)
    for i in 0...numHyps do
      let i := numHyps - 1 - i
      let hyp := mkBVEq (mkSt (i + 1)) (mkCollapsing ops (mkSt i) sizeHyps)
      goalType := .forallE (Name.mkSimple s!"h{i}") hyp goalType .default

    let label := label.getString
    let incTime ← measureTac tacInc goalType
    IO.println s!"measurement: {label}_inc {incTime.toFloat / 1000.0} s"
    let nonIncTime ← measureTac tacNonInc goalType
    IO.println s!"measurement: {label}_noninc {nonIncTime.toFloat / 1000.0} s"
    IO.println s!"measurement: {label}_speedup {nonIncTime.toFloat / incTime.toFloat} x"

structure Test where
  name : String
  numHyps : Nat
  sizeHyps : Nat
  numGoals : Nat

def benchTestVectors (bigHyp mediumHyp smallHyp manyGoals manyHyps : Nat) : Array Test := #[
  ⟨"one_big_hyp_many_goals", 1, bigHyp, manyGoals⟩,
  ⟨"one_big_hyp_one_goal", 1, bigHyp, 1⟩,
  ⟨"many_small_hyps_many_goals", manyHyps, smallHyp, manyGoals⟩,
  ⟨"many_small_hyps_one_goal", manyHyps, smallHyp, 1⟩,
  ⟨"many_medium_hyps_many_goals", manyHyps, mediumHyp, manyGoals⟩,
  ⟨"many_medium_hyps_one_goal", manyHyps, mediumHyp, 1⟩,
]

set_option warn.sorry false
open Lean Elab Command in
run_cmd do
  let bench := (← IO.getEnv "TEST_BENCH") == some "1"
  let vectors := if bench then benchTestVectors 512 32 8 16 32 else benchTestVectors 2 2 2 2 2
  for vector in vectors do
    let { name, numHyps, sizeHyps, numGoals } := vector
    let name := Syntax.mkStrLit name
    let numHyps := Syntax.mkNumLit (toString numHyps)
    let sizeHyps := Syntax.mkNumLit (toString sizeHyps)
    let numGoals := Syntax.mkNumLit (toString numGoals)
    elabCommand (← `(command| #queries $name $numHyps $sizeHyps $numGoals))
end BVDecideIncremental
