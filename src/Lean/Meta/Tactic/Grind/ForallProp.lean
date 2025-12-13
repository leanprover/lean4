/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
public import Init.Grind.Propagator
import Init.Simproc
import Init.Grind.Norm
import Lean.Meta.Tactic.Grind.PropagatorAttr
import Lean.Meta.Tactic.Grind.Propagate
import Lean.Meta.Tactic.Grind.Internalize
import Lean.Meta.Tactic.Grind.Simp
import Lean.Meta.Tactic.Grind.Anchor
import Lean.Meta.Tactic.Grind.EqResolution
import Lean.Meta.Tactic.Grind.SynthInstance
public section
namespace Lean.Meta.Grind
/--
Propagator for dependent forall terms
`forall (h : p), q[h]` where p is a proposition.
-/
def propagateForallPropUp (e : Expr) : GoalM Unit := do
  let .forallE n p q bi := e | return ()
  trace_goal[grind.debug.forallPropagator] "{e}"
  if !q.hasLooseBVars then
    propagateImpliesUp p q
  else
    unless (← isEqTrue p) do return
    trace_goal[grind.debug.forallPropagator] "isEqTrue, {e}"
    let h₁ ← mkEqTrueProof p
    let qh₁ := q.instantiate1 (mkOfEqTrueCore p h₁)
    let r ← preprocess qh₁
    let q := mkLambda n bi p q
    let q' := r.expr
    internalize q' (← getGeneration e)
    trace_goal[grind.debug.forallPropagator] "q': {q'} for{indentExpr e}"
    let h₂ ← r.getProof
    let h := mkApp5 (mkConst ``Lean.Grind.forall_propagator) p q q' h₁ h₂
    pushEq e q' h
where
  propagateImpliesUp (a b : Expr) : GoalM Unit := do
    unless (← alreadyInternalized b) do return ()
    if (← isEqFalse a <&&> isProp b) then
      -- a = False → (a → b) = True
      pushEqTrue e <| mkApp3 (mkConst ``Grind.imp_eq_of_eq_false_left) a b (← mkEqFalseProof a)
    else if (← isEqTrue a <&&> isProp b) then
      -- a = True → (a → b) = b
      pushEq e b <| mkApp3 (mkConst ``Grind.imp_eq_of_eq_true_left) a b (← mkEqTrueProof a)
    else if (← isEqTrue b <&&> isProp a) then
      -- b = True → (a → b) = True
      pushEqTrue e <| mkApp3 (mkConst ``Grind.imp_eq_of_eq_true_right) a b (← mkEqTrueProof b)
    else if (← isEqFalse b <&&> isEqTrue e <&&> isProp a) then
      -- (a → b) = True → b = False → a = False
      pushEqFalse a <| mkApp4 (mkConst ``Grind.eq_false_of_imp_eq_true) a b (← mkEqTrueProof e) (← mkEqFalseProof b)

private def isEqTrueHyp? (proof : Expr) : Option FVarId := Id.run do
  let_expr eq_true _ p := proof | return none
  let .fvar fvarId := p | return none
  return some fvarId

/-- Similar to `mkEMatchTheoremWithKind?`, but swallow any exceptions. -/
private def mkEMatchTheoremWithKind'? (origin : Origin) (proof : Expr) (kind : EMatchTheoremKind) (prios : SymbolPriorities) : MetaM (Option EMatchTheorem) := do
  try
    -- **Note**: for local theorems, we want to use very general patterns, this is why we set `minIndexable := true`
    -- The same approach is used in Z3.
    mkEMatchTheoremWithKind? origin #[] proof kind prios (groundPatterns := false) (minIndexable := true)
  catch _ =>
    return none

/-- Returns `true` if `thm?` is none or its patterns are different from the ones in `thm'` -/
private def isNewPat (patternsFoundSoFar : Array (List Expr)) (thm' : EMatchTheorem) : Bool :=
  patternsFoundSoFar.all fun ps => thm'.patterns != ps

/--
Given a proof of an `EMatchTheorem`, returns `true`, if there are no
anchor references restricting the search, or there is an anchor
references `ref` s.t. `ref` matches `proof`.
-/
def checkAnchorRefsEMatchTheoremProof (proof : Expr) : GrindM Bool := do
  let some anchorRefs ← getAnchorRefs | return true
  let anchor ← getAnchor (← inferType proof)
  return anchorRefs.any (·.matches anchor)

private def addLocalEMatchTheorems (e : Expr) : GoalM Unit := do
  let proof ← mkEqTrueProof e
  let origin ← if let some fvarId := isEqTrueHyp? proof then
    pure <| .fvar fvarId
  else
    let idx ← modifyGet fun s => (s.ematch.nextThmIdx, { s with ematch.nextThmIdx := s.ematch.nextThmIdx + 1 })
    pure <| .local ((`local).appendIndexAfter idx)
  let proof := mkOfEqTrueCore e proof
  -- **Note**: Do we really need to restrict the instantiation of local theorems?
  -- **Note**: Should we distinguish anchors restricting case-splits and local theorems?
  unless (← checkAnchorRefsEMatchTheoremProof proof) do return ()
  let size := (← get).ematch.newThms.size
  let gen ← getGeneration e
  let mut patternsFoundSoFar := #[]
  let symPrios ← getSymbolPriorities
  let minPrio := eval_prio default -- We only consider symbols with default priority and above when collecting singleton patterns.
  let thms ← mkEMatchTheoremUsingSingletonPatterns origin #[] proof minPrio symPrios
  for thm in thms do
    if isNewPat patternsFoundSoFar thm then
      activateTheorem thm gen
      patternsFoundSoFar := patternsFoundSoFar.push thm.patterns
  if let some thm ← mkEMatchTheoremWithKind'? origin proof .leftRight symPrios then
    if isNewPat patternsFoundSoFar thm then
      activateTheorem thm gen
      patternsFoundSoFar := patternsFoundSoFar.push thm.patterns
  if let some thm ← mkEMatchTheoremWithKind'? origin proof .rightLeft symPrios then
    if isNewPat patternsFoundSoFar thm then
      activateTheorem thm gen
      patternsFoundSoFar := patternsFoundSoFar.push thm.patterns
  if (← get).ematch.newThms.size == size then
    if let some thm ← mkEMatchTheoremWithKind'? origin proof (.default false) symPrios then
      activateTheorem thm gen
  if (← get).ematch.newThms.size == size then
    reportIssue! "failed to create E-match local theorem for{indentExpr e}"

def propagateForallPropDown (e : Expr) : GoalM Unit := do
  let .forallE n a b bi := e | return ()
  if (← isEqFalse e) then
    if b.hasLooseBVars || !(← isProp a) then
      let α := a
      let p := b
      -- `e` is of the form `∀ x : α, p x`
      -- Add fact `∃ x : α, ¬ p x`
      let u ← getLevel α
      let prop := mkApp2 (mkConst ``Exists [u]) α (mkLambda n bi α (mkNot p))
      let proof := mkApp3 (mkConst ``Grind.of_forall_eq_false [u]) α (mkLambda n bi α p) (← mkEqFalseProof e)
      addNewRawFact proof prop (← getGeneration e) (.forallProp e)
    else
      let h ← mkEqFalseProof e
      pushEqTrue a <| mkApp3 (mkConst ``Grind.eq_true_of_imp_eq_false) a b h
      pushEqFalse b <| mkApp3 (mkConst ``Grind.eq_false_of_imp_eq_false) a b h
  else if (← isEqTrue e) then
    if let some (e', h') ← eqResolution e then
      trace_goal[grind.eqResolution] "{e}, {e'}"
      let h := mkOfEqTrueCore e (← mkEqTrueProof e)
      let h' := mkApp h' h
      addNewRawFact h' e' (← getGeneration e) (.forallProp e)
    if b.hasLooseBVars then
      unless (← isProp a) do
        /-
        We used to waste a lot of time trying to process terms such as
        ```
        ∀ (h : i + 1 ≤ w), x.abs.getLsbD i = x.abs[i]
        ```
        as E-matching theorems. They are "dependent" implications, and should be handled
        by `propagateForallPropUp`.
        -/
        addLocalEMatchTheorems e
    else
      unless (← alreadyInternalized b) do return ()
      if (← isEqFalse b <&&> isProp a) then
      -- (a → b) = True → b = False → a = False
      pushEqFalse a <| mkApp4 (mkConst ``Grind.eq_false_of_imp_eq_true) a b (← mkEqTrueProof e) (← mkEqFalseProof b)

builtin_grind_propagator propagateExistsDown ↓Exists := fun e => do
  if (← isEqFalse e) then
    let_expr f@Exists α p := e | return ()
    let u := f.constLevels!
    let notP := mkApp (mkConst ``Not) (mkApp p (.bvar 0) |>.headBeta)
    let prop := mkForall `x .default α notP
    let proof := mkApp3 (mkConst ``forall_not_of_not_exists u) α p (mkOfEqFalseCore e (← mkEqFalseProof e))
    addNewRawFact proof prop (← getGeneration e) (.existsProp e)

private def isForallOrNot? (e : Expr) : Option (Name × Expr × Expr) :=
  if let .forallE n d b _ := e then
    some (n, d, b)
  else if e.isAppOfArity ``Not 1 then
    some (`a, e.appArg!, mkConst ``False)
  else
    none

/--
Applies the following rewriting rules:
- `Grind.imp_true_eq`
- `Grind.imp_false_eq`
- `Grind.forall_imp_eq_or`
- `Grind.true_imp_eq`
- `Grind.false_imp_eq`
- `Grind.imp_self_eq`
- `forall_true`
- `forall_false`
- `Grind.forall_or_forall`
- `Grind.forall_forall_or`
- `Grind.forall_and`
-/
builtin_simproc_decl simpForall ((a : _) → _) := fun e => do
  let .forallE varName d b info := e | return .continue
  if !b.hasLooseBVars then
    match_expr d with
    | True => if (← isProp b) then return .done { expr := b, proof? := mkApp (mkConst ``Grind.true_imp_eq) b }
    | False => if (← isProp b) then return .done { expr := mkConst ``True, proof? := mkApp (mkConst ``Grind.false_imp_eq) b }
    | _ =>
    if let .forallE aName α pRaw info' := d then
      if (← pure pRaw.hasLooseBVars <&&> isProp d) then
        let p := mkLambda aName info' α pRaw
        let q := b
        let u ← getLevel α
        let expr := mkOr (mkApp2 (mkConst ``Exists [u]) α (mkLambda aName info' α (mkNot pRaw))) q
        return .visit { expr, proof? := mkApp3 (mkConst ``Grind.forall_imp_eq_or [u]) α p q }
    else match_expr b with
    | True => if (← isProp d) then return .done { expr := mkConst ``True, proof? := mkApp (mkConst ``Grind.imp_true_eq) d }
    | False => if (← isProp d) then return .visit { expr := mkNot d, proof? := mkApp (mkConst ``Grind.imp_false_eq) d }
    | _ => if (← isProp d <&&> isDefEq d b) then
      return .done { expr := mkConst ``True, proof? := mkApp (mkConst ``Grind.imp_self_eq) d }
  else
    -- `b` has loose bound variables
    match_expr d with
    | True =>
      let pTrue := b.instantiate1 (mkConst ``True.intro)
      if (← isProp pTrue) then
        let p := mkLambda varName info d b
        return .done { expr := pTrue, proof? := mkApp (mkConst ``Grind.forall_true) p }
    | False =>
      let p := mkLambda varName info d b
      if (← isDefEq (← inferType p) (mkForall varName info d (mkSort 0))) then
        return .done { expr := mkConst ``True, proof? := mkApp (mkConst ``forall_false) p }
    | _ => pure ()
  -- We try to apply `forall_and`, `forall_or_forall`, and `forall_forall_or` whether `b` has loose bound variables or not.
  if b.isApp && b.getAppNumArgs == 2 then
    let .const bDeclName _ := b.appFn!.appFn! | return .continue
    if bDeclName == ``Or then
      let left  := b.appFn!.appArg!
      let right := b.appArg!
      let α := d
      if let some (bName, βRaw, qRaw) := isForallOrNot? left then
        let pRaw := right
        let p := mkLambda varName info α pRaw
        let q := mkLambda varName info α (mkLambda bName .default βRaw qRaw)
        let β := mkLambda varName info α βRaw
        let u ← getLevel α
        let v ← withLocalDeclD varName α fun a => getLevel (βRaw.instantiate1 a)
        let expr := mkForall varName info α (mkForall bName .default βRaw (mkOr qRaw (pRaw.liftLooseBVars 0 1)))
        return .visit { expr, proof? := mkApp4 (mkConst ``Grind.forall_forall_or [u, v]) α β p q }
      else if let some (bName, βRaw, qRaw) := isForallOrNot? right then
        let pRaw := left
        let p := mkLambda varName info α pRaw
        let q := mkLambda varName info α (mkLambda bName .default βRaw qRaw)
        let β := mkLambda varName info α βRaw
        let u ← getLevel α
        let v ← withLocalDeclD varName α fun a => getLevel (βRaw.instantiate1 a)
        let expr := mkForall varName info α (mkForall bName .default βRaw (mkOr (pRaw.liftLooseBVars 0 1) qRaw))
        return .visit { expr, proof? := mkApp4 (mkConst ``Grind.forall_or_forall [u, v]) α β p q }
    else if bDeclName == ``And then
      let pRaw := b.appFn!.appArg!
      let qRaw := b.appArg!
      let p := mkLambda varName info d pRaw
      let q := mkLambda varName info d qRaw
      let expr := mkAnd (mkForall varName info d pRaw) (mkForall varName info d qRaw)
      let u ← getLevel d
      return .visit { expr, proof? := mkApp3 (mkConst ``Grind.forall_and [u]) d p q }
  -- None of the rules were applicable
  return .continue

/--
Applies the following rewriting rules:
- `Grind.exists_or`
- `Grind.exists_and_left`
- `Grind.exists_and_right`
- `Grind.exists_prop`
- `Grind.exists_const`
-/
builtin_simproc_decl simpExists (Exists _) := fun e => do
  let_expr ex@Exists α fn := e | return .continue
  let .lam x _ b _ := fn | return .continue
  if b.isApp && b.getAppNumArgs == 2 then
    let .const bDeclName _ := b.appFn!.appFn! | return .continue
    if bDeclName == ``Or then
      let pRaw := b.appFn!.appArg!
      let qRaw := b.appArg!
      let p := mkLambda x .default α pRaw
      let q := mkLambda x .default α qRaw
      let u := ex.constLevels!
      let expr := mkOr (mkApp2 ex α p) (mkApp2 ex α q)
      return .visit { expr, proof? := mkApp3 (mkConst ``Grind.exists_or u) α p q }
    else if bDeclName == ``And then
      let pRaw := b.appFn!.appArg!
      let qRaw := b.appArg!
      if !pRaw.hasLooseBVars then
        let b := pRaw
        let p := mkLambda x .default α qRaw
        let expr := mkAnd b (mkApp2 ex α p)
        let u := ex.constLevels!
        return .visit { expr, proof? := mkApp3 (mkConst ``Grind.exists_and_left u) α p b }
      else if !qRaw.hasLooseBVars then
        let p := mkLambda x .default α pRaw
        let b := qRaw
        let expr := mkAnd (mkApp2 ex α p) b
        let u := ex.constLevels!
        return .visit { expr, proof? := mkApp3 (mkConst ``Grind.exists_and_right u) α p b }
  if !b.hasLooseBVars then
    if (← isProp α) then
      let expr := mkAnd α b
      return .visit { expr, proof? := mkApp2 (mkConst ``Grind.exists_prop) α b }
    else
      let u := ex.constLevels!
      let nonempty := mkApp (mkConst ``Nonempty u) α
      if let some nonemptyInst ← synthInstanceMeta? nonempty then
        return .visit { expr := b, proof? := mkApp3 (mkConst ``Grind.exists_const u) α nonemptyInst b }
  return .continue

def addForallSimproc (s : Simprocs) : CoreM Simprocs := do
  let s ← s.add ``simpForall (post := true)
  s.add ``simpExists (post := true)

end Lean.Meta.Grind
