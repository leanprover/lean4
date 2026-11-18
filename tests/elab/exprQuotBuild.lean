/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Reser
-/
import Lean

/-!
# Comprehensive Tests for Term-Position `` `(expr[rel]| t) `` Building

Covers spec §4 requirements:
- Compile-time closed templates with runtime `$e` splice substitution (`MetaM`, `TacticM`,
  `TermElabM`, `StateT`, polymorphic `[MonadLiftT MetaM m]`).
- Zero beta-reduction (`$P $y` stays `.app`), pointer sharing (`$x + $x`), zero runtime mvar
  allocation for splices, and preservation of caller metavariables inside splices.
- `refine` hole semantics (`?h`, `?_`, shared `?h`, distinct `?_`, fresh per call, `Prop` &
  dependent hole types).
- Strict compile-time errors on unintended `_`, unresolved implicits/universes, failed concrete TC,
  non-splice-dependent stuck TC, unannotated `?h`, out-of-scope `$x`, non-`MetaM` targets, `/sym`.
- Runtime splice type checking under `rel` (defaulting to `defeq`, adjusted by `/reducible`,
  `/instances`, `/structural`, `[±items]`, `[$d]`, `±flags`) and dependent instance synthesis.
- Template deduplication (`exprTmplExt`), closed `ResolvedExprMatchRel` hoisting, and
  `subterms`/`match`/`ctx.fill` round-trips.
-/

namespace ExprQuotBuildTest

open Lean Meta Elab Tactic

def myDefAlias := Nat
abbrev myRedAlias := Nat

private def check (cond : Bool) (msg : String) : MetaM Unit := do
  unless cond do
    throwError msg

private def tryBuild (x : MetaM Expr) : MetaM (Except String Expr) := do
  try
    return .ok (← x)
  catch ex =>
    return .error (← ex.toMessageData.toString)

/-! ## 1. Compile-time strictness errors (`#guard_msgs`) -/

/--
error: don't know how to synthesize placeholder
context:
⊢ Nat
-/
#guard_msgs in
def badUnderscore : MetaM Expr := `(expr| (_ : Nat) + 1)

/-- error: Failed to infer type of binder `x` -/
#guard_msgs in
def badUnannotatedLam : MetaM Expr := `(expr| fun x => x)

/--
error: don't know how to synthesize implicit argument `α`
  @List.nil ?m.1
context:
⊢ Type ?u.2
-/
#guard_msgs in
def badImplicitNil : MetaM Expr := `(expr| List.nil)

/--
error: invalid `expr` quotation: unresolved universe level metavariables in
  Sort ?u.2
-/
#guard_msgs in
def badSortLevel : MetaM Expr := `(expr| Sort _)

/--
error: invalid `expr` quotation: unresolved universe level metavariables in
  PUnit
-/
#guard_msgs in
def badPUnitLevel : MetaM Expr := `(expr| PUnit)

/--
error: failed to synthesize instance of type class
  HAdd Nat String ?m.5

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
def badConcreteTC : MetaM Expr := `(expr| 1 + "hello")

/--
error: failed to synthesize
  ToString ?m.1

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
def badStuckTCUnderscore : MetaM Expr := `(expr| toString _)

/--
error: failed to synthesize
  ToString ?m.1

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
def badStuckTCHole : MetaM Expr := `(expr| toString ?h)

/--
error: invalid `expr` quotation: hole `?h` has unresolved type; add a type annotation `(?h : T)`
-/
#guard_msgs in
def badUnannotatedHole : MetaM Expr := `(expr| ?h)

/--
error: invalid `expr` quotation: hole `?_` has unresolved type; add a type annotation `(?_ : T)`
-/
#guard_msgs in
def badUnannotatedAnonHole : MetaM Expr := `(expr| ?_)

/--
error: don't know how to synthesize placeholder for argument `tail`
context:
⊢ List ?m.1
-/
#guard_msgs in
def badConsTailHole (x : Expr) : MetaM Expr := `(expr| @List.cons _ $x _)

/--
error: don't know how to synthesize placeholder for argument `isLt`
context:
⊢ 0 < 3
-/
#guard_msgs in
def badFinProofHole : MetaM Expr := `(expr| @Fin.mk 3 0 _)

/-- error: unknown identifier `missingSplice` in `$`-pin (did you mean `?missingSplice`?) -/
#guard_msgs in
def badUnknownSplice : MetaM Expr := `(expr| $missingSplice + 1)

/-- error: expected `$e` splice; use `?_` for a metavariable hole -/
#guard_msgs in
def badDollarUnderscore : MetaM Expr := `(expr| $_ + 1)

/--
error: type mismatch
  `(expr| 1 + 2)
has type
  MetaM Expr
but is expected to have type
  Id Expr
-/
#guard_msgs in
def badWrongMonadId : Id Expr := `(expr| 1 + 2)

/--
error: type mismatch
  `(expr| 1 + 2)
has type
  MetaM Expr
but is expected to have type
  CoreM Expr
-/
#guard_msgs in
def badWrongMonadCore : CoreM Expr := `(expr| 1 + 2)

/--
error: expr quotation `/sym` building engine is not implemented yet (Spike B / B5)
-/
#guard_msgs in
def badSymStub : MetaM Expr := `(expr/sym| 1 + 2)

/--
error: invalid relation item `-ExprQuotBuildTest.myDefAlias`: `structural` does not unfold `ExprQuotBuildTest.myDefAlias` by default
-/
#guard_msgs in
def badStructuralNegItem (a : Expr) : MetaM Expr :=
  `(expr/structural [-myDefAlias]| ($a : Nat))

/-! ## 2. Template deduplication, monad lifting, & closed relation hoisting -/

def polyBuild [Monad m] [MonadLiftT MetaM m] (a b : Expr) : m Expr :=
  `(expr| $a + $b)

def tacBuild (a b : Expr) : TacticM Expr :=
  `(expr| $a + $b)

def termBuild (a b : Expr) : TermElabM Expr :=
  `(expr| $a + $b)

def stateBuild (a b : Expr) : StateT Nat MetaM Expr := do
  modify (· + 1)
  `(expr| $a + $b)

def sharedTmplDedup (a b x y : Expr) : MetaM (Expr × Expr) := do
  let e1 ← `(expr| Nat.add $a $b)
  let e2 ← `(expr/structural| Nat.add $x $y)
  return (e1, e2)

def nestedSpliceBuild (a b c : Expr) : MetaM Expr := do
  `(expr| Nat.mul $(← `(expr| Nat.add $a $b)) $c)

/-! ## 3. Runtime tests: sharing, zero-beta, holes, relations, dependent TCs, round-trips -/

#guard_msgs in
#eval show MetaM Unit from do
  -- 1. Zero beta-reduction on `$P $y` and `fun x => $P x`.
  let natTy := mkConst ``Nat
  let pFun := mkLambda `x .default natTy (mkApp2 (mkConst ``Nat.add) (mkBVar 0) (mkNatLit 1))
  let y := mkNatLit 41
  let appExpr ← `(expr| $pFun $y)
  check (appExpr.isApp && ptrEq appExpr.appFn! pFun && ptrEq appExpr.appArg! y)
    "$P $y must preserve exact .app node without beta-reduction"
  Meta.check appExpr

  let hoLam ← `(expr| fun x => $pFun x)
  match hoLam with
  | .lam _ dom (.app fn (.bvar 0)) _ =>
    check (dom == natTy && ptrEq fn pFun) "fun x => $P x domain/body mismatch"
  | _ => throwError "expected unreduced .lam body (.app pFun (.bvar 0)), got {hoLam}"
  Meta.check hoLam

  -- Explicit normalization outside the quotation still works cleanly.
  let reduced ← Core.betaReduce appExpr
  check (reduced == mkApp2 (mkConst ``Nat.add) (mkNatLit 41) (mkNatLit 1))
    "explicit Core.betaReduce mismatch"

  -- 2. Pointer sharing on repeated `$x` and zero runtime mvar allocation for splices.
  let x := mkNatLit 7
  let dbl ← `(expr| $x + $x)
  match dbl with
  | .app (.app _ a1) a2 =>
    check (ptrEq x a1 && ptrEq x a2) "repeated `$x` must preserve pointer sharing"
  | _ => throwError "expected binary app for `$x + $x`, got {dbl}"

  let a := mkNatLit 1
  let b := mkNatLit 2
  let mvsBefore := (← getMCtx).mvarCounter
  let typedAdd ← `(expr| ($a : Nat) + ($b : Nat))
  let mvsAfter := (← getMCtx).mvarCounter
  check (mvsAfter == mvsBefore) "typed splice build must allocate zero runtime metavariables"
  Meta.check typedAdd

  -- Nested splice & template deduplication (`sharedTmplDedup`).
  let nested ← nestedSpliceBuild (mkNatLit 2) (mkNatLit 3) (mkNatLit 4)
  check (nested == mkApp2 (mkConst ``Nat.mul) (mkApp2 (mkConst ``Nat.add) (mkNatLit 2) (mkNatLit 3))
    (mkNatLit 4)) "nested splice build mismatch"
  let env ← getEnv
  let mut tmplCount := 0
  for (n, _) in env.constants do
    if (``sharedTmplDedup).isPrefixOf n && n.toString.contains "exprTmpl" then
      tmplCount := tmplCount + 1
  check (tmplCount == 1) s!"expected 1 deduplicated exprTmpl const, got {tmplCount}"

  -- Polymorphic & monad lifts.
  check ((← polyBuild a b) == typedAdd) "polyBuild mismatch"
  let ((stRes, stCnt)) ← (stateBuild a b).run 0
  check (stRes == typedAdd && stCnt == 1) "stateBuild mismatch"

  -- 3. `refine` holes (`?h`, `?_`), shared `?h`, distinct `?_`, fresh per call, Prop & dep.
  let holeNamed ← `(expr| (?h : Nat) + (?h : Nat))
  let mvsNamed ← getMVars holeNamed
  let [mvH] := mvsNamed.toList
    | throwError "expected 1 shared mvar for `?h + ?h`, got {mvsNamed.size}"
  let dH ← mvH.getDecl
  check (dH.userName == `h && dH.kind matches .syntheticOpaque && dH.type == natTy)
    "`?h` must be `.syntheticOpaque` named `h : Nat`"

  let holeAnon ← `(expr| (?_ : Nat) + (?_ : Nat))
  let mvsAnon ← getMVars holeAnon
  let [mvA0, mvA1] := mvsAnon.toList
    | throwError "expected 2 anon mvars for `?_ + ?_`, got {mvsAnon.size}"
  check (mvA0 != mvA1) "two `?_` holes must be distinct metavariables"
  for mv in [mvA0, mvA1] do
    let d ← mv.getDecl
    check (d.userName == .anonymous && d.kind matches .syntheticOpaque)
      "`?_` must be anonymous `.syntheticOpaque`"

  let holeCall1 ← `(expr| (?h : Nat))
  let holeCall2 ← `(expr| (?h : Nat))
  check (holeCall1 != holeCall2) "separate quotation calls must allocate fresh hole mvars"

  let propP := mkConst ``True
  let hProp ← `(expr| (?hp : $propP))
  check (hProp.isMVar && (← hProp.mvarId!.getDecl).kind matches .syntheticOpaque &&
    (← inferType hProp) == propP) "`(?hp : $propP)` failed for `Prop` splice"

  let depHoles ← `(expr| @Sigma.mk Nat Fin ?n ?f)
  let depMVs ← getMVars depHoles
  let [mvN, mvF] := depMVs.toList
    | throwError "expected 2 dependent Sigma holes, got {depMVs.size}"
  check ((← mvN.getDecl).userName == `n && (← mvF.getDecl).userName == `f)
    "dependent Sigma hole names mismatch"
  check ((← instantiateMVars (← mvF.getDecl).type) == mkApp (mkConst ``Fin) (mkMVar mvN))
    "dependent `?f` type must reference `?n`"
  Meta.check depHoles

  -- Caller metavariable inside splice stays untouched.
  let callerMV ← mkFreshExprMVar (some natTy) .natural `callerHole
  let builtCaller ← `(expr| ($callerMV : Nat) + 1)
  check (!(← callerMV.mvarId!.isAssigned)) "caller metavariable must remain unassigned"
  match builtCaller with
  | .app (.app _ lhs) _ => check (ptrEq lhs callerMV) "caller mvar pointer must stay intact"
  | _ => throwError "expected binary app for builtCaller"

  -- 4. Runtime splice type checking under configured relations & flags.
  withLocalDeclD `aDef (mkConst ``myDefAlias) fun aDef =>
  withLocalDeclD `aRed (mkConst ``myRedAlias) fun aRed => do
    check (← tryBuild `(expr| ($aDef : Nat))).isOk "default `.defeq` must accept myDefAlias"
    check (!(← tryBuild `(expr[-myDefAlias]| ($aDef : Nat))).isOk)
      "`[-myDefAlias]` must reject myDefAlias"
    check (!(← tryBuild `(expr/reducible| ($aDef : Nat))).isOk)
      "`/reducible` must reject semireducible myDefAlias"
    check (← tryBuild `(expr/reducible [+myDefAlias]| ($aDef : Nat))).isOk
      "`/reducible [+myDefAlias]` must accept myDefAlias"
    check (← tryBuild `(expr/reducible| ($aRed : Nat))).isOk
      "`/reducible` must accept reducible myRedAlias"
    check (!(← tryBuild `(expr/structural| ($aRed : Nat))).isOk)
      "`/structural` must reject reducible myRedAlias"
    check (← tryBuild `(expr/structural [myDefAlias]| ($aDef : Nat))).isOk
      "`/structural [myDefAlias]` must accept myDefAlias"

  let betaTy := mkApp (mkLambda `z .default (mkSort 1) natTy) natTy
  withLocalDeclD `aBeta betaTy fun aBeta => do
    check (← tryBuild `(expr| ($aBeta : Nat))).isOk "default `/defeq` must reduce beta in type"
    check (!(← tryBuild `(expr/defeq -beta| ($aBeta : Nat))).isOk)
      "`/defeq -beta` must reject unreduced beta type"
    check (← tryBuild `(expr/structural +beta| ($aBeta : Nat))).isOk
      "`/structural +beta` must reduce beta in type"

  withLetDecl `D (mkSort 1) natTy fun d =>
  withLocalDeclD `xd d fun xd => do
    check (!(← tryBuild `(expr/defeq -zeta| ($xd : Nat))).isOk)
      "`/defeq -zeta` must block local let unfolding"
    check (← tryBuild `(expr/defeq [$d] -zeta| ($xd : Nat))).isOk
      "`/defeq [$d] -zeta` must allow unfolding `$d`"
    check (← tryBuild `(expr/defeq [$(d)] -zeta| ($xd : Nat))).isOk
      "`/defeq [$(d)] -zeta` must allow unfolding `$(d)`"

  -- 5. Runtime dependent type-class synthesis (success & failure) & splice type errors.
  let eAdd ← `(expr| $a + $b)
  let eEq ← `(expr| $a == $b)
  let eIte ← `(expr| if $(mkConst ``True) then $a else $b)
  let eStr ← `(expr| toString $a)
  let eCons ← `(expr| List.cons $a [])
  for built in [eAdd, eEq, eIte, eStr, eCons] do
    Meta.check built

  let three := mkNatLit 3
  let four := mkNatLit 4
  withLocalDeclD `fa (mkApp (mkConst ``Fin) three) fun fa =>
  withLocalDeclD `fb (mkApp (mkConst ``Fin) three) fun fb =>
  withLocalDeclD `fc (mkApp (mkConst ``Fin) four) fun fc => do
    Meta.check (← `(expr| ($fa : Fin $three) + ($fb : Fin $three)))
    Meta.check (← `(expr| ($fa : Fin $three) == ($fb : Fin $three)))
    match ← tryBuild `(expr| ($fa : Fin $three) == ($fc : Fin $three)) with
    | .ok _ => throwError "expected runtime splice mismatch for Fin 4 vs Fin 3"
    | .error msg =>
      check (msg.contains "expr quotation splice type mismatch")
        s!"unexpected Fin mismatch message: {msg}"

  withLocalDeclD `α (mkSort 1) fun α =>
  withLocalDeclD `instAdd (mkApp (mkConst ``Add [0]) α) fun _ =>
  withLocalDeclD `xα α fun xα =>
  withLocalDeclD `yα α fun yα => do
    let builtLocalTC ← `(expr| ($xα : $α) + ($yα : $α))
    Meta.check builtLocalTC

  let sHi := mkStrLit "hi"
  match ← tryBuild `(expr| $a == $sHi) with
  | .ok _ => throwError "expected runtime splice type mismatch for `1 == \"hi\"`"
  | .error msg =>
    check (msg.contains "expr quotation splice type mismatch")
      s!"unexpected splice mismatch message: {msg}"

  match ← tryBuild `(expr| toString $pFun) with
  | .ok _ => throwError "expected runtime TC failure for `toString (Nat → Nat)`"
  | .error msg =>
    check (msg.contains "expr quotation failed to synthesize dependent instance")
      s!"unexpected runtime TC failure message: {msg}"

  match ← tryBuild `(expr| if $a then $a else $b) with
  | .ok _ => throwError "expected runtime Prop type mismatch on `if 1 ...`"
  | .error msg =>
    check (msg.contains "expr quotation splice type mismatch")
      s!"unexpected ite condition mismatch message: {msg}"

  -- 5b. B3 polish: loose-bvar splice precheck & caller mvar with unknown type.
  let loose := mkBVar 0
  match ← tryBuild `(expr| $loose + $a) with
  | .ok _ => throwError "expected runtime error for loose bound variable splice"
  | .error msg =>
    check (msg.contains "expr quotation splice expression contains loose bound variable")
      s!"unexpected loose-bvar error message: {msg}"

  let unkTy ← mkFreshTypeMVar
  let unkMV ← mkFreshExprMVar (some unkTy)
  match ← tryBuild `(expr| ($unkMV : Nat) + $a) with
  | .ok _ => throwError "expected runtime splice type mismatch for unknown-type caller mvar"
  | .error msg =>
    check (msg.contains "expr quotation splice type mismatch")
      s!"unexpected unknown-type caller mvar message: {msg}"
    check (!(← unkMV.mvarId!.isAssigned) && !(← unkTy.mvarId!.isAssigned))
      "failed splice check must not mutate caller metavariables or their types"

  -- 6. Round-trip `subterms` + pattern `match` + term-position build + `ExprContext.fill`.
  let mulExpr := mkApp2 (mkConst ``Nat.mul) (mkNatLit 2) (mkNatLit 3)
  let root := mkApp2 (mkConst ``Nat.add) mulExpr (mkNatLit 4)
  let mut rewritten := root
  for (sub, ctx) in subterms root do
    if let `(expr| Nat.mul ?u ?v) := sub then
      let repl ← `(expr| Nat.add $v $u)
      rewritten := ctx.fill repl
      break
  let expectedRewritten :=
    mkApp2 (mkConst ``Nat.add) (mkApp2 (mkConst ``Nat.add) (mkNatLit 3) (mkNatLit 2)) (mkNatLit 4)
  check (rewritten == expectedRewritten) "subterms + match + build + fill round-trip failed"
  Meta.check rewritten

-- Tactic integration test: build goal-closing expression with `?h` refine hole inside `TacticM`.
theorem tacticBuildAndRefine (n : Nat) : n + 0 = n := by
  run_tac do
    let nExpr := (← getLocalDeclFromUserName `n).toExpr
    let pat ← `(expr| @Nat.add_zero $nExpr)
    let goal ← getMainGoal
    goal.assign pat

-- Pretty-printer spacing for relation items and flags (`ppSpace` checks).
/--
info: "`(expr/reducible [+Nat.add, -Nat.mul] -eta| 1 + 2)"
"match (modulo := defeq [+Nat.add] +zeta) (0 : Nat) with\n| _ => 1"
"match (modulo := [+Nat.add] +zeta) (0 : Nat) with\n| _ => 1"
"match (modulo := +zeta -eta) (0 : Nat) with\n| _ => 1"
-/
#guard_msgs in
#eval show TermElabM Unit from do
  let env ← getEnv
  for src in [
    "`(expr/reducible[+Nat.add, -Nat.mul]-eta| 1 + 2)",
    "match (modulo := defeq[+Nat.add]+zeta) (0 : Nat) with | _ => 1",
    "match (modulo := [+Nat.add]+zeta) (0 : Nat) with | _ => 1",
    "match (modulo := +zeta -eta) (0 : Nat) with | _ => 1"
  ] do
    let .ok stx := Parser.runParserCategory env `term src | throwError "parse failed: {src}"
    IO.println (repr (← PrettyPrinter.ppTerm ⟨stx⟩).pretty)

end ExprQuotBuildTest
