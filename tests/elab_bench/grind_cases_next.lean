import Lean

/-!
Benchmark for the cost of a single `cases_next` in the interactive `sym` flow.

The goal contains one `if-then-else` hypothesis (the only split candidate) and one
large BitVec equation (a chain of `&&&`/`|||`/`^^^`/`~~~` of length `n`). The reported
`split_n` measurement is the time of `cases_next; all_goals sorry` alone, obtained by
subtracting the setup time (`intros; internalize_all; sorry`) from the full run.

`split_n` used to grow quadratically in `n`: `[grind hom]`/cutsat pushed chain-sized `Nat`
facts into the `newRawFacts` queue during internalization, the first `cases_next`
preprocessed them once per subgoal, and `markNestedSubsingletons` called `inferType` on
every node. This benchmark guards the fixes: draining the queue before the `cases`
tactics, and the quick proof/`Decidable` classifier in `markNestedSubsingletons`.
-/

namespace GrindCasesNext

open Lean Meta Elab Term

set_option maxHeartbeats 0
set_option maxRecDepth 0
set_option warn.sorry false

private def bvTy : Expr := mkApp (mkConst ``BitVec) (mkNatLit 64)

private structure Ops where
  and : Expr
  or : Expr
  xor : Expr
  compl : Expr

private def Ops.mk' : MetaM Ops := do
  let hInst (cls : Name) : MetaM Expr :=
    synthInstance (mkApp3 (mkConst cls [0, 0, 0]) bvTy bvTy bvTy)
  return {
    and := ← hInst ``HAnd, or := ← hInst ``HOr, xor := ← hInst ``HXor
    compl := ← synthInstance (mkApp (mkConst ``Complement [0]) bvTy)
  }

private def mkBinOp (fn : Name) (inst a b : Expr) : Expr :=
  mkApp6 (mkConst fn [0, 0, 0]) bvTy bvTy bvTy inst a b

private def Ops.mkCompl (ops : Ops) (a : Expr) : Expr :=
  mkApp3 (mkConst ``Complement.complement [0]) bvTy ops.compl a

private def mkBVEq (a b : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [1]) bvTy a b

private def mkChain (ops : Ops) (n : Nat) (x y z w : Expr) : Expr := Id.run do
  let mut e := x
  for i in 0...n do
    e := match i % 3 with
      | 0 => ops.mkCompl (mkBinOp ``HAnd.hAnd ops.and e y)
      | 1 => mkBinOp ``HOr.hOr ops.or e (ops.mkCompl z)
      | _ => mkBinOp ``HXor.hXor ops.xor e (ops.mkCompl w)
  return e

private def mkGoal (n : Nat) : MetaM Expr := do
  let ops ← Ops.mk'
  withLocalDeclD `b (mkConst ``Bool) fun b =>
  withLocalDeclD `p bvTy fun p =>
  withLocalDeclD `q bvTy fun q =>
  withLocalDeclD `r bvTy fun r =>
  withLocalDeclD `x bvTy fun x =>
  withLocalDeclD `y bvTy fun y =>
  withLocalDeclD `z bvTy fun z =>
  withLocalDeclD `w bvTy fun w => do
    let c := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) b (mkConst ``Bool.true)
    let hIte := mkApp5 (mkConst ``ite [1]) (mkSort 0) c
      (← synthInstance (mkApp (mkConst ``Decidable) c)) (mkBVEq p q) (mkBVEq q r)
    let hBig := mkBVEq (mkChain ops n x y z w) w
    withLocalDeclD `hIte hIte fun hIte =>
    withLocalDeclD `hBig hBig fun hBig =>
      mkForallFVars #[b, p, q, r, x, y, z, w, hIte, hBig] (mkConst ``False)

private def measureTac (tac : TSyntax `tactic) (goal : Expr) : TermElabM Float := do
  let mvar ← mkFreshExprMVar goal
  let start ← IO.monoNanosNow
  discard <| Tactic.run mvar.mvarId! (Tactic.evalTactic tac)
  let stop ← IO.monoNanosNow
  return (stop - start).toFloat / 1e9

open Command in
elab "#cases_next_bench " n:num : command => do
  let n := n.getNat
  let tacSetup ← `(tactic| sym => intros; internalize_all; sorry)
  let tacSplit ← `(tactic| sym =>  intros; internalize_all; cases_next; all_goals sorry)
  liftTermElabM do
    let goal ← mkGoal n
    let setup ← measureTac tacSetup goal
    let split ← measureTac tacSplit goal
    IO.println s!"measurement: split_{n} {split - setup} s"

open Command in
run_cmd do
  for n in #[400, 800, 1600, 3200, 6400] do
    elabCommand (← `(command| #cases_next_bench $(Syntax.mkNumLit (toString n))))

end GrindCasesNext
