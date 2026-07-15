import Lean.Meta.Sym.Pattern
import Lean.Meta.Sym.Intro

/-! MWE for the zeta that `+jp` spec construction hits.

`Sym.introN` introduces a nondep `let` (`have`) as a *dependent* ldecl: `Intro.lean` calls
`mkLetDecl` without threading the letE's `nondep` flag. `mkSpecTheorem` then runs
`Sym.preprocessType`, whose `zetaReduce` unfolds the dependent fvar, so a spec keyed on
`@fv joinParams` is re-keyed on the join-point body. Marking the fvar nondep preserves it. -/

open Lean Meta Sym

/--
info: [Sym.introN: isNondep=false] preprocessType: 3 = 3
---
info: [fixed:     isNondep=true]  preprocessType: f✝ 3 = f✝ 3
-/
#guard_msgs in
run_meta do
  let nat := mkConst ``Nat
  let arrow : Expr := .forallE `_ nat nat .default              -- Nat → Nat
  let val ← withLocalDeclD `x nat fun x => mkLambdaFVars #[x] x -- `fun x => x`
  let target := Expr.letE `f arrow val (mkConst ``True) (nondep := true)  -- nondep `have f`
  let mvar ← mkFreshExprMVar target
  SymM.run do
    let .goal newDecls newGoal ← Sym.introN mvar.mvarId! 1 | return
    -- (1) as `Sym.introN` leaves it: dependent, so `preprocessType` zeta-reduces `f 3`
    newGoal.withContext do
      let f := mkFVar newDecls[0]!
      let ty ← mkEq (mkApp f (mkNatLit 3)) (mkApp f (mkNatLit 3))
      let nd := ((← getLCtx).find? newDecls[0]!).get!.isNondep
      logInfo m!"[Sym.introN: isNondep={nd}] preprocessType: {← Sym.preprocessType ty}"
    -- (2) with the fix (nondep): `preprocessType` preserves `f 3`
    newGoal.modifyLCtx fun lctx => lctx.modifyLocalDecl newDecls[0]! (·.setNondep true)
    newGoal.withContext do
      let f := mkFVar newDecls[0]!
      let ty ← mkEq (mkApp f (mkNatLit 3)) (mkApp f (mkNatLit 3))
      let nd := ((← getLCtx).find? newDecls[0]!).get!.isNondep
      logInfo m!"[fixed:     isNondep={nd}]  preprocessType: {← Sym.preprocessType ty}"
