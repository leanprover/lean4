import Lean

/-!
Tests for `Lean.MVarId.firstHyp?`, `Lean.MVarId.firstHyp`, `Lean.Elab.Tactic.firstHyp?`,
and `Lean.Elab.Tactic.firstHyp`:
- `MVarId.firstHyp` / `firstHyp?` in `MetaM`, `ExceptT`, and `TacticM`
- Default `reverse := true` (newest first) vs `reverse := false` (oldest first)
- Pattern matching `(h, ty)` via `` `(expr/reducible| ...) `` and nested
  `firstHyp (except := [h1])` with `$P` pins for multi-hypothesis matching
- Atomic `Tactic.SavedState` rollback (mvars, goals, message log, info trees, term state)
- Interactive recovery safety (`withRecover true` + failing `evalTactic` never admits `sorry` or
  leaks stray error messages)
- Automatic `withMainContext` handling immediately after `intro`
- Skipping `.implDetail` declarations, instantiating assigned mvars in hypothesis types before `f`,
  and `"firstHyp: no hypothesis matched"` / `"No goals to be solved"` errors
-/

namespace FirstHypTest

open Lean Meta Elab Tactic

opaque pTag : Nat → Prop
opaque qTag : Nat → Prop
@[reducible] def pTagRed (n : Nat) : Prop := pTag n

private def check (cond : Bool) (msg : String) : MetaM Unit := do
  unless cond do
    throwError msg

/-! ## 1. `MVarId.firstHyp?` / `MVarId.firstHyp` in `MetaM` and `ExceptT` -/

/-- info: (some (3), some (1), [3, 2, 1], [1, 2, 3], some (2), true, true, true) -/
#guard_msgs in
run_meta do
  let (revHit, fwdHit, rv, fv, exHit, noneIsNone, exErr, excOk) ←
    withLocalDeclD `h1 (mkApp (mkConst ``pTag) (mkNatLit 1)) fun h1 =>
    withLocalDeclD `h2 (mkApp (mkConst ``pTag) (mkNatLit 2)) fun _ =>
    withLocalDeclD `h3 (mkApp (mkConst ``pTag) (mkNatLit 3)) fun h3 => do
      let goal ← mkFreshExprMVar (some (mkConst ``True))
      let mvarId := goal.mvarId!
      let revHit ← mvarId.firstHyp? fun _ ty => do
        match ty with
        | `(expr| pTag ?n) =>
          let some k ← getNatValue? n | throwError "not nat"
          return k
        | _ => throwError "no match"
      let fwdHit ← mvarId.firstHyp? (reverse := false) fun _ ty => do
        match ty with
        | `(expr| pTag ?n) =>
          let some k ← getNatValue? n | throwError "not nat"
          return k
        | _ => throwError "no match"
      let revVisited ← IO.mkRef #[]
      let noneHit : Option Unit ← mvarId.firstHyp? fun _ ty => do
        match ty with
        | `(expr| pTag ?n) =>
          if let some k ← getNatValue? n then
            revVisited.modify (·.push k)
          throwError "reject"
        | _ => throwError "no match"
      let fwdVisited ← IO.mkRef #[]
      let _ : Option Unit ← mvarId.firstHyp? (reverse := false) fun _ ty => do
        match ty with
        | `(expr| pTag ?n) =>
          if let some k ← getNatValue? n then
            fwdVisited.modify (·.push k)
          throwError "reject"
        | _ => throwError "no match"
      let exHit ← mvarId.firstHyp? (except := [h3, mkMData .empty h1]) fun _ ty => do
        match ty with
        | `(expr| pTag ?n) =>
          let some k ← getNatValue? n | throwError "not nat"
          return k
        | _ => throwError "no match"
      let exErr ← try
        let _ ← mvarId.firstHyp fun _ _ => (throwError "fail" : MetaM Unit)
        pure false
      catch ex =>
        pure ((← ex.toMessageData.toString) == "firstHyp: no hypothesis matched")
      -- Verify `ExceptT` works via `{ε : Type}` polymorphism on `MVarId.firstHyp?`.
      let excRes ← (mvarId.firstHyp? (m := ExceptT String MetaM) fun _ ty =>
        match ty with
        | `(expr| pTag 2) => return 22
        | _               => throwThe Exception (.error .missing "skip")).run
      let excOk : Bool := match excRes with
        | .ok (some 22) => true
        | _             => false
      let rv ← revVisited.get
      let fv ← fwdVisited.get
      return (revHit, fwdHit, rv.toList, fv.toList, exHit, noneHit.isNone, exErr, excOk)
  logInfo m!"({revHit}, {fwdHit}, {rv}, {fv}, {exHit}, {noneIsNone}, {exErr}, {excOk})"

/--
error: firstHyp: no hypothesis matched
-/
#guard_msgs in
run_meta do
  let goal ← mkFreshExprMVar (some (mkConst ``True))
  goal.mvarId!.firstHyp fun _ _ => (pure () : MetaM Unit)

/-! ## 2. `MetaM` rollback, `.implDetail` skip, and assigned mvar instantiation -/

/-- info: (true, (true, true)) -/
#guard_msgs in
run_meta do
  let sideMVar ← mkFreshExprMVar (some (mkConst ``Nat))
  let hypMVar ← mkFreshExprMVar (some (mkConst ``Nat))
  hypMVar.mvarId!.assign (mkNatLit 42)
  let ok ←
    withLocalDeclD `hOld (mkApp (mkConst ``pTag) hypMVar) fun hOld =>
    withLocalDecl `hImpl .default (mkApp (mkConst ``pTag) (mkNatLit 99))
      (kind := .implDetail) fun _ =>
    withLocalDeclD `hNew (mkApp (mkConst ``qTag) (mkNatLit 10)) fun hNew => do
      let goal ← mkFreshExprMVar (some (mkConst ``True))
      let seen ← IO.mkRef #[]
      let res ← goal.mvarId!.firstHyp fun h ty => do
        seen.modify (·.push h)
        if h == hNew then
          sideMVar.mvarId!.assign (mkNatLit 777)
          throwError "fail newest arm after mutating mvar"
        -- Must arrive with `hypMVar` already instantiated and `hImpl` skipped.
        check (!(← sideMVar.mvarId!.isAssigned)) "mvar leaked across MetaM firstHyp"
        check (!ty.hasMVar) "assigned mvar in hyp type was not instantiated"
        match ty with
        | `(expr/structural| pTag 42) => return (h == hOld)
        | _ => throwError "unexpected ty: {ty}"
      let visited ← seen.get
      return (res, visited == #[hNew, hOld], !(← sideMVar.mvarId!.isAssigned))
  logInfo m!"{ok}"

/-! ## 3. `Tactic.firstHyp`, `MVarId.firstHyp` in `TacticM`, `except`, `$P`, `withMainContext` -/

private def solveByModusPonens : TacticM Unit := do
  firstHyp fun h1 ty1 => do
    match ty1 with
    | `(expr/reducible| pTag ?X) =>
      let patTy1 := ty1
      firstHyp (except := [h1]) fun h2 ty2 => do
        match ty2 with
        | `(expr/reducible| $patTy1 → ?Q) =>
          let goal ← getMainGoal
          unless ← isDefEq Q (← goal.getType) do
            throwError "consequent mismatch"
          goal.assign (mkApp h2 h1)
          replaceMainGoal []
        | _ => throwError "not implication"
    | _ => throwError "not pTag"

#guard_msgs in
theorem modusPonensExample (a b : Nat) (h1 : pTagRed a) (h2 : pTag a → qTag b)
    (h3 : pTag b) : qTag b := by
  run_tac solveByModusPonens

/-
Verify `firstHyp` works immediately after `intro` without explicit `withMainContext`,
`MVarId.firstHyp?`/`MVarId.firstHyp` work directly in `TacticM`, `reverse := true` vs `false`
ordering works, and `except := [h1]` skips `h1` in nested calls.
-/
/-- info: (some (30), some (10), some (20), true, true) -/
#guard_msgs in
example : pTag 10 → pTag 20 → pTag 30 → True := by
  intro h1 h2 h3
  run_tac do
    -- Executed directly after `intro` without an outer `withMainContext`:
    let newest? ← firstHyp? fun _ ty => do
      match ty with
      | `(expr/reducible| pTag ?n) =>
        let some k ← getNatValue? n | throwError "not nat"
        return k
      | _ => throwError "no"
    let oldest? ← firstHyp? (reverse := false) fun _ ty => do
      match ty with
      | `(expr/reducible| pTag ?n) =>
        let some k ← getNatValue? n | throwError "not nat"
        return k
      | _ => throwError "no"
    -- With `except := [h1]`, reflexive `pTag ?_` on `h1` must find a distinct `h2 ≠ h1`.
    let distinctPair ← firstHyp fun h1 ty1 =>
      match ty1 with
      | `(expr/reducible| pTag ?_) =>
        firstHyp (except := [h1]) fun h2 ty2 =>
          match ty2 with
          | `(expr/reducible| pTag ?_) => return (h1 != h2)
          | _                          => throwError "no"
      | _ => throwError "no"
    let (directTacticM?, directHit) ← withMainContext do
      let lctx ← getLCtx
      let some h1Decl := lctx.findFromUserName? `h1 | throwError "missing h1"
      let some h3Decl := lctx.findFromUserName? `h3 | throwError "missing h3"
      let goal ← getMainGoal
      let d? ← goal.firstHyp? (except := [mkFVar h3Decl.fvarId]) fun _ ty => do
        match ty with
        | `(expr/reducible| pTag ?n) =>
          let some k ← getNatValue? n | throwError "not nat"
          return k
        | _ => throwError "no"
      let dHit ← goal.firstHyp fun h ty =>
        match ty with
        | `(expr| pTag 10) => return (h == mkFVar h1Decl.fvarId)
        | _                => throwError "no"
      return (d?, dHit)
    logInfo m!"({newest?}, {oldest?}, {directTacticM?}, {directHit}, {distinctPair})"
  exact trivial

/-! ## 4. Atomic `Tactic.SavedState` rollback (mvars, goals, messages, info trees, term state) -/

/-- info: (true, true, true, true, true, true, true, true) -/
#guard_msgs in
example : pTag 1 → pTag 2 → pTag 2 := by
  intro h1 h2
  run_tac withEnableInfoTree true do
    let sideMVar ← mkFreshExprMVar (some (mkConst ``Nat))
    let goalsBefore ← getGoals
    let msgCountBefore := (← Core.getMessageLog).toList.length
    let infoCountBefore := (← getInfoTrees).size
    let levelNamesBefore ← Term.getLevelNames

    -- First, verify `firstHyp?` returns `none` and rolls back when all arms fail.
    let noneRes : Option Unit ← firstHyp? fun h _ => do
      sideMVar.mvarId!.assign (mkNatLit 99)
      let g1 ← mkFreshExprMVar (some (mkConst ``True))
      let g2 ← mkFreshExprMVar (some (mkConst ``True))
      replaceMainGoal [g1.mvarId!, g2.mvarId!]
      logInfo m!"stray info from failing arm {h}"
      logWarning m!"stray warning from failing arm {h}"
      pushInfoLeaf (.ofTermInfo {
        elaborator := `test
        stx := Syntax.missing
        lctx := ← getLCtx
        expectedType? := none
        expr := h
      })
      Term.setLevelNames [`bogusLevel]
      throwError "fail all"

    let afterNoneOk :=
      noneRes.isNone &&
      !(← sideMVar.mvarId!.isAssigned) &&
      (← getGoals) == goalsBefore &&
      (← Core.getMessageLog).toList.length == msgCountBefore &&
      (← getInfoTrees).size == infoCountBefore &&
      (← Term.getLevelNames) == levelNamesBefore

    -- Next, verify arm 1 (`h1` with `reverse := false`) mutates everything, fails, and rolls
    -- back 100% before arm 2 (`h2`) inspects state and closes the goal.
    let mutatedRef ← IO.mkRef (false, false)
    let arm2Checks ← firstHyp (reverse := false) fun h ty => do
      if ty == mkApp (mkConst ``pTag) (mkNatLit 1) then
        sideMVar.mvarId!.assign (mkNatLit 123)
        let g1 ← mkFreshExprMVar (some (mkConst ``True))
        let g2 ← mkFreshExprMVar (some (mkConst ``True))
        replaceMainGoal [g1.mvarId!, g2.mvarId!]
        logInfo m!"leaked info"
        logWarning m!"leaked warning"
        pushInfoLeaf (.ofTermInfo {
          elaborator := `test
          stx := Syntax.missing
          lctx := ← getLCtx
          expectedType? := none
          expr := h
        })
        Term.setLevelNames [`bogusLevel2]
        let msgsGrew := (← Core.getMessageLog).toList.length > msgCountBefore
        let infoGrew := (← getInfoTrees).size > infoCountBefore
        mutatedRef.set (msgsGrew, infoGrew)
        throwError "arm 1 failed"
      let (msgsGrew, infoGrew) ← mutatedRef.get
      let mvarClean := !(← sideMVar.mvarId!.isAssigned)
      let goalsClean := (← getGoals) == goalsBefore
      let msgsClean := (← Core.getMessageLog).toList.length == msgCountBefore
      let infoClean := (← getInfoTrees).size == infoCountBefore
      let levelsClean := (← Term.getLevelNames) == levelNamesBefore
      let goal ← getMainGoal
      unless ← isDefEq ty (← goal.getType) do
        throwError "wrong hyp"
      goal.assign h
      replaceMainGoal []
      return (afterNoneOk, msgsGrew, infoGrew, mvarClean, goalsClean, msgsClean,
        infoClean, levelsClean)
    let (a, b, c, d, e, f, g, h) := arm2Checks
    logInfo m!"({a}, {b}, {c}, {d}, {e}, {f}, {g}, {h})"

/-! ## 5. Interactive recovery safety (`withRecover true` + failing `evalTactic`) -/

/-- info: (true, true, true, true) -/
#guard_msgs in
theorem recoverSafetyTest (hGood : qTag 2) (hBad1 : pTag 1) (hBad2 : pTag 2) (b : Bool) :
    qTag 2 := by
  run_tac do
    let origGoal ← getMainGoal
    let msgCountBefore := (← Core.getMessageLog).toList.length
    let visited ← IO.mkRef #[]
    let (visitedAll, expectedCount) ← withMainContext do
      let lctx ← getLCtx
      let expectedOrder := #[`b, `hBad2, `hBad1, `hGood].filterMap fun n =>
        (lctx.findFromUserName? n).map (mkFVar ·.fvarId)
      let bId := mkIdent `b
      let hBad1Id := mkIdent `hBad1
      let hGoodId := mkIdent `hGood
      withRecover true do
        firstHyp fun h ty => do
          visited.modify (·.push h)
          if ty.isConstOf ``Bool then
            -- Under `recover := true`, failing `cases` branches would admit `sorry` without
            -- `withoutRecover`.
            let bTgt ← `(Lean.Parser.Tactic.elimTarget| $bId:term)
            evalTactic (← `(tactic|
              cases $bTgt with | true => exact $hBad1Id | false => exact $hBad1Id))
          else if ty == mkApp (mkConst ``pTag) (mkNatLit 2) then
            -- Under `errToSorry := true`, unknown idents would elaborate to `sorry`.
            evalTactic (← `(tactic| exact nonexistentIdentForFirstHypTest))
          else if ty == mkApp (mkConst ``pTag) (mkNatLit 1) then
            evalTactic (← `(tactic| exact $hBad1Id))
          else
            evalTactic (← `(tactic| exact $hGoodId))
      let visitedExprs ← visited.get
      return (visitedExprs == expectedOrder, expectedOrder.size == 4)
    let proof ← instantiateMVars (mkMVar origGoal)
    let noSorry := !proof.hasSorry
    let noErrors := !(← Core.getMessageLog).hasErrors
    let sameMsgs := (← Core.getMessageLog).toList.length == msgCountBefore
    logInfo m!"({visitedAll && expectedCount}, {noSorry}, {noErrors}, {sameMsgs})"

/-- info: (true, true, true) -/
#guard_msgs in
run_meta do
  let ok ← Term.TermElabM.run' do
    withLocalDeclD `hNat (mkConst ``Nat) fun _ => do
      let g ← mkFreshExprMVar (some (mkConst ``False))
      let msgBefore := (← Core.getMessageLog).toList.length
      let threw ←
        try
          discard <| Tactic.run g.mvarId! do
            withRecover true do
              firstHyp fun _ _ => do
                evalTactic (← `(tactic| exact nonexistentIdentForFirstHypTest2))
          pure false
        catch ex =>
          pure ((← ex.toMessageData.toString) == "firstHyp: no hypothesis matched")
      let gProof ← instantiateMVars g
      let clean := !(gProof.hasSorry) && !(← g.mvarId!.isAssigned) &&
        (← Core.getMessageLog).toList.length == msgBefore
      return (threw, clean)
  logInfo m!"({ok.1}, {ok.2}, true)"

/-! ## 6. `Tactic.firstHyp` `.implDetail` skip, mvar instantiation, and error cases -/

/-- info: (true, true) -/
#guard_msgs in
run_meta do
  let mv ← mkFreshExprMVar (some (mkConst ``Nat))
  mv.mvarId!.assign (mkNatLit 7)
  let res ←
    withLocalDecl `hImpl .default (mkApp (mkConst ``pTag) (mkNatLit 99))
      (kind := .implDetail) fun _ =>
    withLocalDeclD `hInst (mkApp (mkConst ``pTag) mv) fun hInst => do
      let g ← mkFreshExprMVar (some (mkConst ``True))
      Term.TermElabM.run' do
        let out ← IO.mkRef (false, false)
        discard <| Tactic.run g.mvarId! do
          firstHyp fun h ty => do
            let okH := h == hInst
            let okTy := !ty.hasMVar && ty == mkApp (mkConst ``pTag) (mkNatLit 7)
            out.set (okH, okTy)
            (← getMainGoal).assign (mkConst ``True.intro)
            replaceMainGoal []
        out.get
  logInfo m!"{res}"

/--
error: firstHyp: no hypothesis matched
-/
#guard_msgs in
example : True := by
  run_tac firstHyp fun _ _ => (throwError "unreachable" : TacticM Unit)

/--
error: firstHyp: no hypothesis matched
-/
#guard_msgs in
example (h : Nat) : True := by
  run_tac firstHyp fun _ _ => (throwError "never succeeds" : TacticM Unit)

/--
error: No goals to be solved
-/
#guard_msgs in
example : True := by
  exact trivial
  run_tac firstHyp fun _ _ => pure ()

end FirstHypTest
