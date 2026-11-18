/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Reser
-/
import Lean

/-!
Comprehensive tests for `` `(expr/sym| ...) `` matching and term building via `MonadSym`:
- `MonadLiftT MetaM GrindTacticM` non-hijack check + `GrindTacticM` / `SymM` / stacked monads.
- `/sym` term building: maximal sharing (`sym.debug := true`, `checkMaxShared`), `foldProjs`,
  zero beta-reduction, pointer sharing, runtime `.syntheticOpaque` `?h`/`?_` holes, caller
  mvar preservation, universe params, splice type checking, and dependent instance synthesis.
- `/sym` pattern matching: nonlinear `?x + ?x`, wildcards & ignored proofs, `$e` pins (with
  proof irrelevance and `let` fvars), `letE` / `zetaDelta` / `eta` / offsets / raw `.proj`
  scrutinees, zero leaked temp mvars/level-mvars, and `unresolvedInsts` rejection.
- Strict compile-time and runtime validation rejecting non-`MonadSym` monads, `[items]`,
  local `$x` items, and disabled `-inst`/`-beta`/`-zeta`/`-proj`/`-eta` flags.
-/

namespace ExprQuotSymTest

open Lean Meta Elab Tactic
open Lean.Meta.Sym (SymM isMaxShared isSameExpr)
open Lean.Elab.Tactic.Grind (GrindTacticM)

set_option sym.debug true

/--
info: instMonadLiftTOfMonadLift MetaM (StateRefT' IO.RealWorld Tactic.Grind.State TermElabM) GrindTacticM
-/
#guard_msgs in
#synth MonadLiftT MetaM Lean.Elab.Tactic.Grind.GrindTacticM

private def check (cond : Bool) (msg : String) : MetaM Unit := do
  unless cond do
    throwError msg

private def withTestGrindTacticM (k : GrindTacticM α) : MetaM α := do
  let params ← Grind.mkDefaultParams {}
  Grind.GrindM.run (params := params) do
    let methods ← Grind.getMethods
    let grindCtx ← readThe Meta.Grind.Context
    let symCtx ← readThe Sym.Context
    let grindState ← get
    let symState ← getThe Sym.State
    let ctx : Tactic.Grind.Context := {
      recover := false, elaborator := `test,
      ctx := grindCtx, sctx := symCtx, methods, params
    }
    let state : Tactic.Grind.State := { grindState, symState, goals := [] }
    Term.TermElabM.run' do
      let (a, _) ← Tactic.Grind.GrindTacticM.run k ctx state
      return a

/-! ## 1. Polymorphic `[MonadSym]` & stacked monads -/

def polyBuildAndMatch [Monad m] [Meta.MonadSym m] (a : Expr) : m (Option (Expr × Expr)) := do
  let t ← `(expr/sym| $a + 1)
  match t with
  | `(expr/sym| ?x + ?y) => return some (x, y)
  | _                    => return none

def stackedSymMatch (e : Expr) : StateT Nat SymM (Option Expr) := do
  let n ← get
  set (n + 1)
  match e with
  | `(expr/sym| ?a + $a) => return some a
  | _                    => return none

def grindTacticSymTest : GrindTacticM Unit := do
  -- `do`-block inference without explicit annotation on `(expr/sym| ...)`
  let a := mkNatLit 7
  let t ← `(expr/sym| ($a, 1).1)
  match t with
  | `(expr/sym| Prod.fst (?x, 1)) =>
    if x != mkNatLit 7 then
      throwError "unexpected capture in GrindTacticM: {x}"
  | _ => throwError "failed match in GrindTacticM: {t}"

run_meta do
  SymM.run do
    let a := mkNatLit 3
    let some (x, y) ← polyBuildAndMatch a
      | throwError "polyBuildAndMatch failed"
    x.checkMaxShared "polyBuild x"
    y.checkMaxShared "polyBuild y"
    check (x == a) "expected x == 3"
    check (y == (← `(expr/sym| (1 : Nat)))) "expected y == 1"
    let dbl := ← `(expr/sym| $a + $a)
    let (res?, cnt) ← (stackedSymMatch dbl).run 0
    check (cnt == 1) "expected StateT counter 1"
    check (res? == some a) "expected stacked StateT SymM nonlinear match"
  withTestGrindTacticM grindTacticSymTest

/-! ## 2. `/sym` term building (`(expr/sym| t)`) -/

def unboxedWrap (x : Nat) : Nat := x + 1

class CustomSymOp (α : Type) where
  op : α → α

instance : CustomSymOp Nat where
  op := Nat.succ

run_meta SymM.run do
  -- 2a. Closed template + projection folding + maximal sharing
  let closed ← `(expr/sym| (1, 2).1)
  closed.checkMaxShared "closed"
  check (closed.find? (·.isProj)).isNone "expected foldProjs to eliminate `.proj`"

  -- 2b. Unshared MetaM splice becomes maximally shared & preserves pointer sharing
  let rawA := mkApp2 (mkConst ``Nat.add) (mkNatLit 2) (mkNatLit 3)
  check (!(← isMaxShared rawA)) "expected fresh rawA to start unshared"
  let built ← `(expr/sym| $rawA + $rawA)
  built.checkMaxShared "built $rawA + $rawA"
  let argR := built.appArg!
  let argL := built.appFn!.appArg!
  check (isSameExpr argL argR) "expected identical pointer for repeated splice `$rawA + $rawA`"

  -- 2c. Zero beta-reduction on `$P $y`
  let idLam := mkLambda `x .default (mkConst ``Nat) (mkBVar 0)
  let zero := mkNatLit 0
  let noBeta ← `(expr/sym| ($idLam : Nat → Nat) $zero)
  noBeta.checkMaxShared "noBeta"
  check noBeta.isApp "expected zero beta reduction on `$P $y`"

  -- 2d. Universe-polymorphic template passes `checkMaxShared`
  let nilNat ← `(expr/sym| (@List.nil Nat))
  nilNat.checkMaxShared "nilNat"
  let idApp ← `(expr/sym| id $zero)
  idApp.checkMaxShared "idApp with levelParams"

  -- 2e. Runtime `.syntheticOpaque` holes (`?h` shared vs `?_` distinct, fresh per call)
  let withSharedHoles ← `(expr/sym| (?h : Nat) + ?h)
  withSharedHoles.checkMaxShared "withSharedHoles"
  let hR := withSharedHoles.appArg!
  let hL := withSharedHoles.appFn!.appArg!
  check (hL.isMVar && hR.isMVar && hL == hR) "expected shared `?h` MVarId"
  check ((← hL.mvarId!.getDecl).kind matches .syntheticOpaque) "expected syntheticOpaque `?h`"

  let withAnon1 ← `(expr/sym| (?_ : Nat) + ?_)
  let withAnon2 ← `(expr/sym| (?_ : Nat) + ?_)
  withAnon1.checkMaxShared "withAnon1"
  let a1L := withAnon1.appFn!.appArg!
  let a1R := withAnon1.appArg!
  let a2L := withAnon2.appFn!.appArg!
  check (a1L.isMVar && a1R.isMVar && a1L != a1R) "expected distinct `?_` MVarIds"
  check (a1L != a2L) "expected fresh hole MVarId per instantiation call"

  -- 2f. Caller metavariable in splice is preserved unassigned
  let callerMV ← mkFreshExprMVar (some (mkConst ``Nat))
  let withCallerMV ← `(expr/sym| $callerMV + 1)
  withCallerMV.checkMaxShared "withCallerMV"
  check (!(← callerMV.mvarId!.isAssigned)) "caller mvar must remain unassigned"

  -- 2g. Dependent typeclass synthesis + runtime splice type mismatch
  let customApp ← `(expr/sym| CustomSymOp.op $zero)
  customApp.checkMaxShared "customApp"
  let badSplice := mkConst ``Bool.true
  let threw ←
    try
      let _ ← `(expr/sym| $badSplice + 1)
      pure false
    catch _ =>
      pure true
  check threw "expected splice type mismatch to fail at runtime"

/-! ## 3. `/sym` matching invariants -/

opaque propCarrier {P : Prop} (h : P) (x : Nat) : Nat

class NeedInst (α : Type) where
  tag : Nat

def withNeedInst {α : Type} [NeedInst α] (x : α) : α := x

opaque UninstType : Type

run_meta SymM.run do
  -- 3a. Skipped proof wildcard `_` works cleanly without false temp-mvar rejection
  let pTrue : Expr := mkConst ``True.intro
  let eProof ← `(expr/sym| propCarrier $pTrue 42)
  match eProof with
  | `(expr/sym| propCarrier _ ?v) =>
    v.checkMaxShared "captured after proof wildcard"
    check (v == (← `(expr/sym| (42 : Nat)))) "expected v == 42"
  | _ => throwError "expected propCarrier match"

  -- 3b. Direct `$h` proof pin succeeds by proof irrelevance
  let pTrue2 ← mkFreshExprMVar (some (mkConst ``True))
  pTrue2.mvarId!.assign (mkConst ``True.intro)
  let thmProof : Expr ← mkAppM ``propCarrier #[pTrue2, mkNatLit 9]
  match thmProof with
  | `(expr/sym| propCarrier $pTrue ?w) =>
    check (w == mkNatLit 9) "expected w == 9"
  | _ => throwError "expected proof pin match by proof irrelevance"

  -- 3c. `$e` pin comparison via `isDefEqS` + `let` fvar `zetaDelta`
  let one := mkNatLit 1
  let two := mkNatLit 2
  let scrutLet ← withLetDecl `k (mkConst ``Nat) one fun kVar => do
    let body ← `(expr/sym| $kVar + 5)
    match body with
    | `(expr/sym| $one + ?rhs) =>
      rhs.checkMaxShared "rhs under let fvar pin"
      check (rhs == (← `(expr/sym| (5 : Nat)))) "expected rhs == 5"
    | _ => throwError "expected `$one + ?rhs` to match `k + 5` under `zetaDelta`"
    match body with
    | `(expr/sym| $two + ?_) => throwError "unexpected match of pin 2 against `k := 1`"
    | _ => pure ()
    pure body
  let _ := scrutLet

  -- 3d. Term `let`, `eta`, offsets (`Nat.succ`, `?n + 1`), and raw Meta `.proj` scrutinees
  let letTerm := mkLet `z (mkConst ``Nat) (mkNatLit 4) (mkApp2 (mkConst ``Nat.add) (mkBVar 0) (mkBVar 0))
  match letTerm with
  | `(expr/sym| Nat.add ?a $a) =>
    a.checkMaxShared "a from letE"
    check (a == mkNatLit 4) "expected letE unfolded to Nat.add 4 4"
  | _ => throwError "expected letE match"

  let etaTerm := mkLambda `x .default (mkConst ``Nat) (mkApp (mkConst ``Nat.succ) (mkBVar 0))
  match etaTerm with
  | `(expr/sym| ?f) =>
    check (f == mkConst ``Nat.succ) "expected eta-reduced `Nat.succ` capture"
  | _ => throwError "expected eta match"

  let rawProj := Expr.proj ``Prod 0 (mkApp4 (mkConst ``Prod.mk [0, 0])
    (mkConst ``Nat) (mkConst ``Nat) (mkNatLit 11) (mkNatLit 12))
  match rawProj with
  | `(expr/sym| Prod.fst (?x, ?y)) =>
    x.checkMaxShared "x from folded proj"
    check (x == (← `(expr/sym| (11 : Nat))) && y == (← `(expr/sym| (12 : Nat))))
      "expected folded proj capture"
  | _ => throwError "expected folded `.proj` match"

  let five : Expr := mkNatLit 5
  match five with
  | `(expr/sym| (?n : Nat) + 1) =>
    n.checkMaxShared "n from offset match on 5"
    check (n == mkNatLit 4) "expected `?n + 1` matching literal `5` to bind `4`"
  | _ => throwError "expected offset match"

  -- 3e. Caller metavariable preserved & ZERO fresh temp mvars leaked on match failure/success
  let callerMV ← mkFreshExprMVar (some (mkConst ``Nat))
  let withMV := mkApp2 (mkConst ``Nat.add) callerMV callerMV
  let mvarCounterBefore := (← getMCtx).mvarCounter
  match withMV with
  | `(expr/sym| Nat.add ?a ?b) =>
    check (a == callerMV && b == callerMV) "expected callerMV preserved in captures"
    check (!(← callerMV.mvarId!.isAssigned)) "callerMV must not be assigned"
  | _ => throwError "expected match on term containing callerMV"
  let mvarCounterAfter := (← getMCtx).mvarCounter
  check (mvarCounterBefore == mvarCounterAfter)
    "pattern matching must not leak fresh temporary metavariables into caller MCtx"

structure WrapNeed (α : Type) where
  val : α

instance instNeedInstWrap {α : Type} [NeedInst α] : NeedInst (WrapNeed α) where
  tag := 1

run_meta SymM.run do
  -- 3f. Reject missing/non-synthesizable pattern instance & unresolved instance constraints
  let fakeInst ← mkFreshExprMVar (some (mkApp (mkConst ``NeedInst) (mkApp (mkConst ``WrapNeed) (mkConst ``UninstType))))
  let wrapVal ← mkFreshExprMVar (some (mkApp (mkConst ``WrapNeed) (mkConst ``UninstType)))
  let badNeed := mkApp3 (mkConst ``withNeedInst)
    (mkApp (mkConst ``WrapNeed) (mkConst ``UninstType)) fakeInst wrapVal
  let mvarCounterPre := (← getMCtx).mvarCounter
  match badNeed with
  | `(expr/sym| @withNeedInst (WrapNeed ?α) (@instNeedInstWrap $α _) ?_) =>
    let _ := α
    throwError "unexpected match when `NeedInst UninstType` has no instance"
  | _ => pure ()
  check ((← getMCtx).mvarCounter == mvarCounterPre)
    "rejected match must not leak temporary mvars"
  match badNeed with
  | `(expr/sym| withNeedInst ?_) => pure ()
  | _ => throwError "expected direct wildcard match"

  -- Reject programmatic pattern with `.instImplicit` binder (`unresolvedInsts` non-empty)
  let mvarCounterPre2 := (← getMCtx).mvarCounter
  let patWithInst : ExprPattern :=
    { levelParams := []
      lam := mkLambda `α .default (mkSort 1)
        (mkLambda `inst .instImplicit (mkApp (mkConst ``NeedInst) (mkBVar 0))
          (mkConst ``True))
      numVars := 2
      namedIdx := #[0]
      firstOrder := #[true, true] }
  let res? ← patWithInst.matchSym? { engine := .sym } (mkConst ``True)
  check res?.isNone "expected unresolved `.instImplicit` instance binder to fail cleanly"
  check ((← getMCtx).mvarCounter == mvarCounterPre2)
    "unresolvedInsts rejection must not leak temporary mvars"

  -- 3g. ReaderT stacked over `GrindTacticM` (verifying polymorphic `[MonadLiftT GrindTacticM m]`)
  pure ()

def readerGrindSym (e : Expr) : ReaderT Nat GrindTacticM (Option Expr) := do
  let _ctx ← read
  match e with
  | `(expr/sym| ?a + ?b) =>
    let res ← `(expr/sym| $b + $a)
    Meta.MonadSym.liftSym (res.checkMaxShared "readerGrindSym swapped")
    return some res
  | _ => return none

run_meta withTestGrindTacticM do
  let e ← `(expr/sym| (1 : Nat) + 2)
  let swapped? ← (readerGrindSym e).run 7
  let expected ← `(expr/sym| (2 : Nat) + 1)
  check (swapped? == some expected) "expected ReaderT GrindTacticM swap"

/-! ## 3h. Head & repeated pins + `GrindM`/`GoalM`/`SimpM`/`DSimpM` + `sym =>` + cache reuse -/

opaque symBinOp : Nat → Nat → Nat

def matchInGrindM (e : Expr) : Meta.Grind.GrindM (Option Expr) := do
  match e with
  | `(expr/sym| ?x + 1) => return some (← `(expr/sym| $x + 2))
  | _                    => return none

def matchInGoalM (e : Expr) : Meta.Grind.GoalM (Option Expr) := do
  match e with
  | `(expr/sym| ?x + 1) => return some (← `(expr/sym| $x + 2))
  | _                    => return none

def matchInSimpM (e : Expr) : Sym.Simp.SimpM (Option Expr) := do
  match e with
  | `(expr/sym| ?x + 1) => return some (← `(expr/sym| $x + 2))
  | _                    => return none

def matchInDSimpM (e : Expr) : Sym.DSimp.DSimpM (Option Expr) := do
  match e with
  | `(expr/sym| ?x + 1) => return some (← `(expr/sym| $x + 2))
  | _                    => return none

def matchHeadAndRepeatedPin (f e : Expr) : SymM Bool :=
  match e with
  | `(expr/sym| $f ?x $x) => let _ := x; return true
  | _                      => return false

def symSiteCacheLoop (e : Expr) : SymM (Nat × Expr) := do
  let mut count := 0
  let mut last ← `(expr/sym| (3, 4).2)
  for _ in *...50 do
    match e with
    | `(expr/sym| ?x * ?y) =>
      let _ := (x, y)
      count := count + 1
    | _ => pure ()
    last ← `(expr/sym| (3, 4).2)
  return (count, last)

run_meta do
  SymM.run do
    let f := mkConst ``symBinOp
    let sameArgs ← `(expr/sym| symBinOp 3 3)
    let diffArgs ← `(expr/sym| symBinOp 3 4)
    check (← matchHeadAndRepeatedPin f sameArgs) "expected head+repeated pin `$f ?x $x` match"
    check (!(← matchHeadAndRepeatedPin f diffArgs)) "expected mismatch on `$f ?x $x`"

    let t ← `(expr/sym| (3 : Nat) + 1)
    let exp ← `(expr/sym| (3 : Nat) + 2)
    check ((← Sym.Simp.SimpM.run' (matchInSimpM t)) == some exp) "expected SimpM match/build"
    check ((← Sym.DSimp.DSimpM.run' (matchInDSimpM t)) == some exp) "expected DSimpM match/build"

    -- Per-site cache reuse: 1st run populates `exprSymPatExt` & `exprSymTmplExt`; subsequent
    -- runs add zero new expressions to `Sym.State.share` or `MCtx`.
    let prodT ← `(expr/sym| (3 : Nat) * 4)
    let shareCount : SymM Nat := do
      return (← getThe Sym.State).share.set.fold (init := 0) fun acc _ => acc + 1
    let (c1, _) ← symSiteCacheLoop prodT
    check (c1 == 50) "expected 50 matches in loop"
    let shareSizeAfterFirst ← shareCount
    let mvarCountAfterFirst := (← getMCtx).mvarCounter
    let (c2, closed) ← symSiteCacheLoop prodT
    check (c2 == 50) "expected 50 matches on cached loop"
    closed.checkMaxShared "cached closed template"
    check ((← shareCount) == shareSizeAfterFirst)
      "cached closed template and pattern reuse must allocate zero extra share nodes"
    check ((← getMCtx).mvarCounter == mvarCountAfterFirst)
      "cached sym site loop must allocate zero caller metavariables"

  let params ← Meta.Grind.mkDefaultParams {}
  Meta.Grind.GrindM.run (params := params) do
    let t ← `(expr/sym| (3 : Nat) + 1)
    let exp ← `(expr/sym| (3 : Nat) + 2)
    check ((← matchInGrindM t) == some exp) "expected GrindM match/build"
    let mv := (← mkFreshExprMVar (mkConst ``True)).mvarId!
    let goal ← Meta.Grind.mkGoalCore mv
    let (goalRes, _) ← (matchInGoalM t).run goal
    check (goalRes == some exp) "expected GoalM match/build"

  -- Env deduplication: repeated identical patterns emit 1 `exprPat` const.
  let env ← getEnv
  let loopPatCount := env.constants.fold (init := 0) fun acc n _ =>
    if (``symSiteCacheLoop).isPrefixOf n && n.toString.contains "exprPat" then acc + 1 else acc
  let loopTmplCount := env.constants.fold (init := 0) fun acc n _ =>
    if (``symSiteCacheLoop).isPrefixOf n && n.toString.contains "exprTmpl" then acc + 1 else acc
  check (loopPatCount == 1) s!"expected 1 exprPat const for symSiteCacheLoop, got {loopPatCount}"
  check (loopTmplCount == 1)
    s!"expected 1 deduplicated exprTmpl const for symSiteCacheLoop, got {loopTmplCount}"

syntax (name := testSymQuotTactic) "test_sym_quot" : grind

@[grind_tactic testSymQuotTactic] def evalTestSymQuotTactic : Grind.GrindTactic := fun _ =>
  Grind.withMainContext do
    let goal ← Grind.getMainGoal
    let tgt ← goal.mvarId.getType
    match tgt with
    | `(expr/sym| ?x + ?y = $y + $x) =>
      let pf ← `(expr/sym| @Nat.add_comm $x $y)
      goal.mvarId.assign pf
      Grind.replaceMainGoal []
    | _ => throwError "unexpected `sym =>` goal: {tgt}"

theorem interactiveSymBlockTest (x y : Nat) : x + y = y + x := by
  sym => test_sym_quot

/-! ## 4. Reject invalid `/sym` relations & monads cleanly -/

/--
error: expr quotation `/sym` requires a `[MonadSym]` monad (e.g. `SymM` or `GrindTacticM`), got expected type
  Id Expr
-/
#guard_msgs in
def rejectSymBuildId : Id Expr := `(expr/sym| 1 + 2)

/--
error: expr quotation matching requires a monad with `[MonadSym]` (e.g. `SymM` or `GrindTacticM`), got result type
  Id Nat
-/
#guard_msgs in
def rejectSymMatchId (e : Expr) : Id Nat :=
  match e with
  | `(expr/sym| ?x) => let _ := x; 1
  | _ => 0

/-- error: expr quotation `/sym` relation does not support `[items]` unfold overrides -/
#guard_msgs in
def rejectSymPatItems (e : Expr) : SymM Nat :=
  match e with
  | `(expr/sym [+Nat.add]| ?x) => let _ := x; return 1
  | _ => return 0

/-- error: expr quotation `/sym` relation does not support local `$x` unfold overrides -/
#guard_msgs in
def rejectSymPatLocalItem (d e : Expr) : SymM Nat :=
  match e with
  | `(expr/sym [+$d]| ?x) => let _ := x; return 1
  | _ => return 0

/-- error: expr quotation `/sym` relation does not support disabling `-zeta` -/
#guard_msgs in
def rejectSymPatNegFlag (e : Expr) : SymM Nat :=
  match e with
  | `(expr/sym -zeta| ?x) => let _ := x; return 1
  | _ => return 0

/-- error: expr quotation `/sym` relation does not support `[items]` unfold overrides -/
#guard_msgs in
def rejectSymBuildItems : SymM Expr := `(expr/sym [+Nat.add]| 1 + 2)

/-- error: expr quotation `/sym` relation does not support disabling `-inst` -/
#guard_msgs in
def rejectSymBuildNegInst : SymM Expr := `(expr/sym -inst| 1 + 2)

/-- error: expr quotation `/sym` relation does not support disabling `-beta` -/
#guard_msgs in
def rejectSymBuildNegBeta : SymM Expr := `(expr/sym -beta| 1 + 2)

/-- error: expr quotation `/sym` relation does not support disabling `-proj` -/
#guard_msgs in
def rejectSymBuildNegProj : SymM Expr := `(expr/sym -proj| 1 + 2)

/-- error: expr quotation `/sym` relation does not support disabling `-eta` -/
#guard_msgs in
def rejectSymBuildNegEta : SymM Expr := `(expr/sym -eta| 1 + 2)

-- Runtime validation on programmatic `ExprMatchRel`
run_meta SymM.run do
  let badRel : ExprMatchRel := { engine := .sym, flags := { eta := some false } }
  let pat : ExprPattern := {
    levelParams := []
    lam         := mkLambda `x .default (mkConst ``Expr) (mkBVar 0)
    numVars     := 1
    namedIdx    := #[]
    firstOrder  := #[false]
  }
  let threw ←
    try
      let _ ← pat.matchSym? badRel (mkNatLit 0)
      pure false
    catch _ =>
      pure true
  check threw "expected runtime reject on `-eta` under `.sym`"

end ExprQuotSymTest
