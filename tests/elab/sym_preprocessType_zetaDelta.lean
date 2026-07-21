import Lean.Meta.Sym

/-!
`Sym.preprocessType` must not zeta-delta ambient let-bound fvars unless explicitly
requested (`zetaDelta := false` by default). Regression test from Sebastian Graf's
vcgen `+jp` report: a spec keyed on `@f joinParams`, where `f` is a join point
introduced by `Sym.introN`, was re-keyed on the join-point body because
`preprocessType` unfolded `f`.
-/

open Lean Meta Sym

/-- info: [dependent ldecl: isNondep=false] preprocessType: f✝ 3 = f✝ 3 -/
#guard_msgs in
run_meta do
  -- Build the goal `have f : Nat → Nat := fun x => x; True` by hand.
  -- This is a nondep `letE`, i.e., what `+jp` join points look like in a goal.
  let nat := mkConst ``Nat
  let arrow : Expr := .forallE `_ nat nat .default
  let val ← withLocalDeclD `x nat fun x => mkLambdaFVars #[x] x
  let target := Expr.letE `f arrow val (mkConst ``True) (nondep := true)
  let mvar ← mkFreshExprMVar target
  SymM.run do
    let .goal newDecls newGoal ← Sym.introN mvar.mvarId! 1 | return
    -- `Sym.introN` leaves `f` as a dependent ldecl. `preprocessType`
    -- must keep `f 3` as is; it used to zeta-delta it to `3`.
    newGoal.withContext do
      let f := mkFVar newDecls[0]!
      let ty ← mkEq (mkApp f (mkNatLit 3)) (mkApp f (mkNatLit 3))
      let nd := ((← getLCtx).find? newDecls[0]!).get!.isNondep
      logInfo m!"[dependent ldecl: isNondep={nd}] preprocessType: {← Sym.preprocessType ty}"
