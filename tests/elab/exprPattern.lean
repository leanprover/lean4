/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Reser
-/
import Lean

/-!
Tests for `Lean.Meta.ExprPattern`, covering:
- `O(|pattern|)` structural matching (wildcard elision, single-entry mvar instantiation, empty-bound
  and closed-subterm `hasAnyFVar` skips, and `O(|pattern|)` unassigned-mvar capture)
- Syntactic/pointer-equality fast path and precomputed closed-proof annotations before proof
  irrelevance
- Structural `.const` and `.sort` universe level checks, repeated pattern `levelParams`, and `+inst`
- Engines (`structural`, `reducible`, `instances`, `defeq`), flags (`inst`, `beta`, `zeta`, `proj`,
  `eta`), nested `let` look-through + re-wrapping, context `let`-fvars, and `<= 2` `isDefEq`
  fail-fast
- Per-site `[items]` runtime cache (`ResolvedExprMatchRel` / `matchSiteOrElse`), `[+simp]`, `-simp`
  updates, and local item validation errors
- `ExprContext.fill`, `localHypTypes`, `localHypDecls`, and lazy DAG-deduplicated `subterms` and
  `matchDiscriminants`
-/

open Lean Meta

namespace ExprPatternTest

/-! ## 1. Compile-time negative tests (`-item`, error messages, pure checks) -/

def sampleDef (n : Nat) : Nat := n + 1

/--
error: invalid relation item `-ExprPatternTest.sampleDef`:
`structural` does not unfold `ExprPatternTest.sampleDef` by default
-/
#guard_msgs (whitespace := lax) in
def rejectMinusConstOnStructural (e : Expr) : MetaM Bool :=
  match e with
  | `(expr/structural[-sampleDef]| ?x) => let _ := x; return true
  | _ => return false

/--
error: invalid relation item `-simp`:
`structural` does not unfold any simp-set definitions by default
-/
#guard_msgs (whitespace := lax) in
def rejectMinusSimpOnStructural (e : Expr) : MetaM Bool :=
  match e with
  | `(expr/structural[-simp]| ?x) => let _ := x; return true
  | _ => return false

def allowMinusAfterPlusMerged (e : Expr) : MetaM Bool :=
  match (modulo := structural[+sampleDef]) e with
  | `(expr[-sampleDef]| sampleDef 0) => return true
  | _ => return false

#guard
  let p : ExprPattern := {
    levelParams := []
    lam         := mkLambda `x .default (mkConst ``Nat) (mkBVar 0)
    numVars     := 1
    namedIdx    := #[0]
    firstOrder  := #[true]
  }
  p.body == mkBVar 0

/-! ## 2. Helpers & definitions for MetaM tests -/

private def check (cond : Bool) (msg : String) : MetaM Unit := do
  unless cond do
    throwError msg

private def checkExprEq (actual expected : Expr) (label : String) : MetaM Unit := do
  unless actual == expected do
    throwError m!"{label}: mismatch\nexpected:\n{expected}\ngot:\n{actual}"

private def checkErrContains (act : MetaM α) (needle : String) : MetaM Unit := do
  try
    let _ ← act
    throwError "expected error containing `{needle}`, but succeeded"
  catch ex =>
    let msg ← ex.toMessageData.toString
    unless msg.contains needle do
      throwError "expected error containing `{needle}`, got:\n{msg}"

@[reducible] def testAbbrev (n : Nat) : Nat := n
def testOpaqueDef (n : Nat) : Nat := n
@[simp] def testSimpDef (n : Nat) : Nat := n
@[simp] def testErasedSimpDef (n : Nat) : Nat := n
attribute [-simp] testErasedSimpDef
@[simp] def cacheDynSimpDef (n : Nat) : Nat := n

def wrapInnerLet (n : Nat) : Nat :=
  let y := Nat.add n (nat_lit 1)
  Nat.succ (Nat.add y y)

def mkDefWithLet : Nat :=
  let y := nat_lit 2
  y

/--
Build a left-leaning `Nat.add` spine of `depth` steps containing `x` at each step and `leaf` at
the bottom.
-/
private def mkDeepSpine (depth : Nat) (x leaf : Expr) : Expr :=
  match depth with
  | 0 => leaf
  | d + 1 => mkApp2 (mkConst ``Nat.add) (mkDeepSpine d x leaf) x

private def mkClosedList (n : Nat) : Expr :=
  let rec go : Nat → Expr → Expr
    | 0, acc => acc
    | k + 1, acc =>
      mkApp3 (mkConst ``List.cons [0]) (mkConst ``Nat) (mkNatLit k) (go k acc)
  go n (mkApp (mkConst ``List.nil [0]) (mkConst ``Nat))

private def mkManyLets (depth : Nat) (inner : Expr) : Expr :=
  match depth with
  | 0 => inner
  | d + 1 =>
    mkLet `v (mkConst ``Nat) (mkNatLit d) (mkManyLets d inner)

structure TestBox where
  fst : Nat
  snd : Nat

class TestTag (α : Type u) where
  tag : Nat

instance : TestTag Nat where
  tag := 42

def useExplicitTag {α : Type u} (inst : TestTag α) (x : α) : α :=
  let _ := inst
  x

@[instance_reducible] def altTagInst : TestTag Nat where
  tag := 99

@[instance_reducible] def defeqTagInst : TestTag Nat := inferInstance

inductive PolyVec (α : Type u) : Nat → Type u where
  | nil  : PolyVec α 0
  | cons : α → PolyVec α n → PolyVec α (n + 1)

/-! ## 3. `O(|pattern|)` structural matching, wildcards, unassigned-mvar capture -/

private def compileWildAddRightPat : MetaM ExprPattern := do
  let natTy := mkConst ``Nat
  let lam :=
    mkLambda `w .default natTy <|
      mkLambda `r .default natTy <|
        mkApp2 (mkConst ``Nat.add) (mkBVar 1) (mkBVar 0)
  ExprPattern.compile {
    levelParams := []
    lam
    numVars     := 2
    namedIdx    := #[1]
    firstOrder  := #[true, true]
  }

private def testWildcardAndUnassignedMVarCapture : MetaM Unit := do
  let pat ← compileWildAddRightPat
  check pat.precomputed "expected precomputed=true on wild add pattern"
  check (pat.captureVars == #[false, true]) "expected wildcard not materialized"
  let rel ← ({ engine := .structural } : ExprMatchRel).resolve
  withLocalDeclD `x (mkConst ``Nat) fun x => do
    let unassignedMv ← mkFreshExprMVar (mkConst ``Nat)
    let bigWildLhs := mkDeepSpine 2000 x unassignedMv
    let assignedMv ← mkFreshExprMVar (mkConst ``Nat)
    assignedMv.mvarId!.assign (mkNatLit 77)
    let scrutinee := mkApp2 (mkConst ``Nat.add) bigWildLhs assignedMv
    let some xs ← pat.matchResolved? rel scrutinee
      | throwError "expected deep spine match"
    check (xs.size == 1) s!"expected 1 binding, got {xs.size}"
    checkExprEq xs[0]! (mkNatLit 77) "assigned rhs mvar"

    -- Unassigned mvar captured directly under named pattern variable `?r`.
    let unassignedTarget := mkApp2 (mkConst ``Nat.add) bigWildLhs unassignedMv
    let some xsUn ← pat.matchResolved? rel unassignedTarget
      | throwError "expected match with unassigned mvar RHS"
    checkExprEq xsUn[0]! unassignedMv "unassigned rhs mvar"

    -- `Nat.add ?l ?r` walking a 2000-step spine ending in an unassigned mvar stays `O(|pattern|)`.
    let natTy := mkConst ``Nat
    let addPat ← ExprPattern.compile {
      levelParams := []
      lam := mkLambda `l .default natTy <| mkLambda `r .default natTy <|
        mkApp2 (mkConst ``Nat.add) (mkBVar 1) (mkBVar 0)
      numVars     := 2
      namedIdx    := #[0, 1]
      firstOrder  := #[true, true]
    }
    let mut cur := bigWildLhs
    for step in *...2000 do
      let some stepRes ← addPat.matchResolved? rel cur
        | throwError s!"expected spine match at step {step}"
      checkExprEq stepRes[1]! x s!"spine rhs at step {step}"
      cur := stepRes[0]!
    checkExprEq cur unassignedMv "spine bottom unassigned mvar"

    -- Nested assigned mvar inside a captured subterm stays uninstantiated under `.structural`
    -- (for `O(|pattern|)` perf), while `instantiateMVars` resolves it cleanly.
    let nestedAssigned ← mkFreshExprMVar (mkConst ``Nat)
    nestedAssigned.mvarId!.assign (mkNatLit 9)
    let nestedCapTerm :=
      mkApp2 (mkConst ``Nat.add) bigWildLhs (mkApp (mkConst ``Nat.succ) nestedAssigned)
    let some xsNested ← pat.matchResolved? rel nestedCapTerm
      | throwError "expected nested assigned mvar match"
    check xsNested[0]!.hasExprMVar "expected uninstantiated nested assigned mvar under structural"
    checkExprEq (← instantiateMVars xsNested[0]!)
      (mkApp (mkConst ``Nat.succ) (mkNatLit 9)) "instantiated nested capture"

    -- Multi-occurrence wildcard must still be captured and checked for equality.
    let lamDupWild :=
      mkLambda `w .default natTy <|
        mkApp2 (mkConst ``Nat.add) (mkBVar 0) (mkBVar 0)
    let dupPat ← ExprPattern.compile {
      levelParams := []
      lam         := lamDupWild
      numVars     := 1
      namedIdx    := #[]
      firstOrder  := #[true]
    }
    check (dupPat.captureVars == #[true]) "expected duplicate wildcard to be captured"
    check (← dupPat.matchResolved? rel (mkApp2 (mkConst ``Nat.add) x x)).isSome
      "duplicate wildcard equal args must match"
    check (← dupPat.matchResolved? rel (mkApp2 (mkConst ``Nat.add) x (mkNatLit 0))).isNone
      "duplicate wildcard distinct args must fail"

#guard_msgs in
#eval show MetaM Unit from testWildcardAndUnassignedMVarCapture

/-! ## 4. Closed-proof precomputation, syntactic fast path, nonlinear proofs -/

private def testProofIrrelevanceAndFastPath : MetaM Unit := do
  let list16 := mkClosedList 16
  let list16Diff :=
    mkApp3 (mkConst ``List.cons [0]) (mkConst ``Nat) (mkNatLit 99) (mkClosedList 15)
  let listPat ← ExprPattern.compile {
    levelParams := []
    lam         := list16
    numVars     := 0
    namedIdx    := #[]
    firstOrder  := #[]
  }
  check listPat.precomputed "expected precomputed=true on list pattern"
  check listPat.closedProofs.isEmpty "closed list of Nat terms must have zero proofs"
  let rel ← ({ engine := .structural } : ExprMatchRel).resolve
  check (← listPat.matchResolved? rel list16).isSome "list16 self match failed"
  check (← listPat.matchResolved? rel list16Diff).isNone "list16 diff unexpectedly matched"

  let eqRefl0 := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit 0)
  let proofPat ← ExprPattern.compile {
    levelParams := []
    lam         := eqRefl0
    numVars     := 0
    namedIdx    := #[]
    firstOrder  := #[]
  }
  check proofPat.precomputed "expected precomputed=true on closed proof pattern"
  check (!proofPat.closedProofs.isEmpty) "expected precomputed closed proof entry"
  let eqNat00 ← mkEq (mkNatLit 0) (mkNatLit 0)
  let eqNat11 ← mkEq (mkNatLit 1) (mkNatLit 1)
  withLocalDeclD `hTrue (mkConst ``True) fun hTrue =>
  withLocalDeclD `hEq0 eqNat00 fun hEq0 =>
  withLocalDeclD `hEq1 eqNat11 fun hEq1 => do
    check (← proofPat.matchResolved? rel hEq0).isSome "proof irrelevance on 0 = 0 failed"
    check (← proofPat.matchResolved? rel hEq1).isNone "1 = 1 matched 0 = 0 proof"
    check (← proofPat.matchResolved? rel hTrue).isNone "True matched Eq proof"
    check (← proofPat.matchResolved? rel (mkNatLit 0)).isNone "Nat matched Eq proof"

    let pairTrue := mkApp4 (mkConst ``And.intro) (mkConst ``True) (mkConst ``True)
      hTrue (mkConst ``True.intro)
    let matchedNonlinear ← match pairTrue with
      | `(expr/structural| And.intro ?p $p) => pure (p == hTrue)
      | _ => pure false
    check matchedNonlinear "nonlinear pin `$p` proof irrelevance failed"

    let binderLam :=
      mkLambda `h .default (mkConst ``True) <|
        mkApp4 (mkConst ``And.intro) (mkConst ``True) (mkConst ``True) (mkBVar 0) (mkBVar 0)
    let nlPat ← ExprPattern.compile {
      levelParams := []
      lam         := binderLam
      numVars     := 1
      namedIdx    := #[0]
      firstOrder  := #[true]
    }
    let some xs ← nlPat.matchResolved? rel pairTrue
      | throwError "expected nonlinear binder proof match"
    checkExprEq xs[0]! hTrue "nonlinear proof binder value"

    -- Runtime fallback for proof containing pattern `levelParam`.
    let polyPat ← ExprPattern.compile {
      levelParams := [`u]
      lam         := mkApp2 (mkConst ``Eq.refl [Level.succ (.param `u)])
        (mkSort (.param `u)) (mkConst ``Nat)
      numVars     := 0
      namedIdx    := #[]
      firstOrder  := #[]
    }
    check polyPat.closedProofs.isEmpty "level-polymorphic proof should not be in closedProofs"
    let eqNatNat ← mkEq (mkConst ``Nat) (mkConst ``Nat)
    withLocalDeclD `hNatEq eqNatNat fun hNatEq => do
      check (← polyPat.matchResolved? rel hNatEq).isSome "poly proof fallback failed"
      check (← polyPat.matchResolved? rel hEq0).isNone "poly proof matched wrong Eq type"

#guard_msgs in
#eval show MetaM Unit from testProofIrrelevanceAndFastPath

/-! ## 5. Universe levels & `.const` checks in `structural` and `+inst` -/

private def testUniverseLevels : MetaM Unit := do
  let relStruct ← ({ engine := .structural } : ExprMatchRel).resolve
  let relStructInst ← ({ engine := .structural, flags := { inst := some true } } :
    ExprMatchRel).resolve

  let nil0 := mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Nat)
  let nil1 :=
    mkApp (mkConst ``List.nil [Level.succ Level.zero]) (mkSort (Level.succ Level.zero))
  let hitNil0 ← match nil0 with
    | `(expr/structural| @List.nil.{0} _) => pure true
    | _ => pure false
  let hitNil1On0 ← match nil1 with
    | `(expr/structural| @List.nil.{0} _) => pure true
    | _ => pure false
  check hitNil0 "@List.nil.{0} failed to match List.nil.{0}"
  check (!hitNil1On0) "@List.nil.{0} unexpectedly matched List.nil.{1}"

  -- Repeated pattern `levelParam` consistency on `.sort` and `.const`.
  let pairSameU := mkApp4 (mkConst ``Prod.mk [1, 1]) (mkSort (.succ .zero)) (mkSort (.succ .zero))
    (mkConst ``Nat) (mkConst ``Bool)
  let pairDiffU := mkApp4 (mkConst ``Prod.mk [1, 2])
    (mkSort (.succ .zero)) (mkSort (.succ (.succ .zero)))
    (mkConst ``Nat) (mkSort (.succ .zero))
  let sortPairLam :=
    mkLambda `a .default (mkSort (.succ (.param `u))) <|
      mkLambda `b .default (mkSort (.succ (.param `u))) <|
        mkApp4 (mkConst ``Prod.mk [Level.succ (.param `u), Level.succ (.param `u)])
          (mkSort (.succ (.param `u))) (mkSort (.succ (.param `u)))
          (mkBVar 1) (mkBVar 0)
  let sortPairPat ← ExprPattern.compile {
    levelParams := [`u]
    lam         := sortPairLam
    numVars     := 2
    namedIdx    := #[]
    firstOrder  := #[true, true]
  }
  check (← sortPairPat.matchResolved? relStruct pairSameU).isSome "same-u sort pair failed"
  check (← sortPairPat.matchResolved? relStruct pairDiffU).isNone "diff-u sort pair matched"

  -- `.const` level param recorded on first occurrence enforced on second occurrence.
  let constLevelPat ← ExprPattern.compile {
    levelParams := [`u, `v]
    lam :=
      mkLambda `α .default (mkSort (.succ (.param `u))) <|
        mkLambda `β .default (mkSort (.succ (.param `v))) <|
          mkApp4 (mkConst ``Prod.mk [Level.succ (.param `u), Level.succ (.param `v)])
            (mkApp (mkConst ``List [Level.param `u]) (mkBVar 1))
            (mkApp (mkConst ``List [Level.param `u]) (mkBVar 0))
            (mkApp (mkConst ``List.nil [Level.param `u]) (mkBVar 1))
            (mkApp (mkConst ``List.nil [Level.param `u]) (mkBVar 0))
    numVars     := 2
    namedIdx    := #[]
    firstOrder  := #[true, true]
  }
  let nilPairSame := mkApp4 (mkConst ``Prod.mk [1, 1])
    (mkApp (mkConst ``List [0]) (mkConst ``Nat))
    (mkApp (mkConst ``List [0]) (mkConst ``Bool))
    (mkApp (mkConst ``List.nil [0]) (mkConst ``Nat))
    (mkApp (mkConst ``List.nil [0]) (mkConst ``Bool))
  let nilPairDiff := mkApp4 (mkConst ``Prod.mk [1, 2])
    (mkApp (mkConst ``List [0]) (mkConst ``Nat))
    (mkApp (mkConst ``List [1]) (mkSort (.succ .zero)))
    (mkApp (mkConst ``List.nil [0]) (mkConst ``Nat))
    (mkApp (mkConst ``List.nil [1]) (mkSort (.succ .zero)))
  check (← constLevelPat.matchResolved? relStruct nilPairSame).isSome
    "same-u const pair failed"
  check (← constLevelPat.matchResolved? relStruct nilPairDiff).isNone
    "diff-u const pair unexpectedly matched"

  -- Independent `_` universe holes on `Type _` must remain independent.
  let twoSortDiff := mkApp4 (mkConst ``Prod.mk [2, 3])
    (mkSort (.succ (.succ .zero))) (mkSort (.succ (.succ (.succ .zero))))
    (mkSort (.succ .zero)) (mkSort (.succ (.succ .zero)))
  let indU ← match twoSortDiff with
    | `(expr/structural| (Type _, Type _)) => pure true
    | _ => pure false
  check indU "independent Type _ universe holes failed"

  -- `+inst` substitutes pattern `levelParams` when checking `[inst]` arguments and enforces `u`.
  let tagNat ← mkAppOptM ``TestTag.tag #[mkConst ``Nat, none]
  let patInstLam :=
    mkLambda `α .default (mkSort (.succ (.param `u))) <|
      mkLambda `s .default (mkSort (.succ (.param `u))) <|
        mkApp4 (mkConst ``Prod.mk [0, Level.succ (.param `u)])
          (mkConst ``Nat) (mkSort (.succ (.param `u)))
          (mkApp2 (mkConst ``TestTag.tag [Level.param `u]) (mkBVar 1)
            (mkApp2 (mkConst ``TestTag.mk [Level.param `u]) (mkBVar 1) (mkNatLit 42)))
          (mkBVar 0)
  let instPolyPat ← ExprPattern.compile {
    levelParams := [`u]
    lam         := patInstLam
    numVars     := 2
    namedIdx    := #[0, 1]
    firstOrder  := #[true, true]
  }
  let targetInstSameU := mkApp4 (mkConst ``Prod.mk [0, 1])
    (mkConst ``Nat) (mkSort (.succ .zero)) tagNat (mkConst ``Nat)
  let targetInstDiffU := mkApp4 (mkConst ``Prod.mk [0, 2])
    (mkConst ``Nat) (mkSort (.succ (.succ .zero))) tagNat (mkSort (.succ .zero))
  check (← instPolyPat.matchResolved? relStruct targetInstSameU).isNone
    "plain structural must reject non-defeq structural instance arg"
  let some instRes ← instPolyPat.matchResolved? relStructInst targetInstSameU
    | throwError "expected +inst level match"
  checkExprEq instRes[0]! (mkConst ``Nat) "+inst arg 0"
  checkExprEq instRes[1]! (mkConst ``Nat) "+inst arg 1"
  check (← instPolyPat.matchResolved? relStructInst targetInstDiffU).isNone
    "+inst must enforce repeated levelParam u across Prod.mk"

#guard_msgs in
#eval show MetaM Unit from testUniverseLevels

/-! ## 6. Engines, flags, nested `let` look-through + rewrap, and 100-`let` fail-fast -/

private def testEnginesFlagsAndRewrap : MetaM Unit := do
  -- `+inst` checks `instImplicit` args by `.instances` defeq, NOT explicit args!
  let instReal ← synthInstance (mkApp (mkConst ``TestTag [0]) (mkConst ``Nat))
  let eExpDefEq ← mkAppM ``useExplicitTag #[mkConst ``defeqTagInst, mkNatLit 1]
  let hitExpStructInst ← match eExpDefEq with
    | `(expr/structural +inst| @useExplicitTag Nat $instReal 1) => pure true
    | _ => pure false
  let hitExpDefeq ← match eExpDefEq with
    | `(expr/defeq| @useExplicitTag Nat $instReal 1) => pure true
    | _ => pure false
  check (!hitExpStructInst) "+inst must not unfold explicit defeqTagInst"
  check hitExpDefeq "defeq must unify defeqTagInst with instReal"

  -- Reducibility boundaries: `testAbbrev` vs `testOpaqueDef`.
  let eAbbrev := mkApp (mkConst ``testAbbrev) (mkNatLit 3)
  let eOpaque := mkApp (mkConst ``testOpaqueDef) (mkNatLit 3)
  check (!(← match eAbbrev with | `(expr/structural| 3) => pure true | _ => pure false))
    "structural must not unfold reducible testAbbrev"
  check (← match eAbbrev with | `(expr/reducible| 3) => pure true | _ => pure false)
    "reducible must unfold testAbbrev"
  check (!(← match eOpaque with | `(expr/reducible| 3) => pure true | _ => pure false))
    "reducible must not unfold testOpaqueDef"
  check (!(← match eOpaque with | `(expr/instances| 3) => pure true | _ => pure false))
    "instances must not unfold testOpaqueDef"
  check (← match eOpaque with | `(expr/defeq| 3) => pure true | _ => pure false)
    "defeq must unfold testOpaqueDef"

  -- `-beta`, `-zeta` (including unused `let` NOT consumed!), `-proj`, `-eta`.
  let natTy := mkConst ``Nat
  let eBeta := mkApp (mkLambda `x .default natTy (mkNatAdd (mkBVar 0) (mkNatLit 1))) (mkNatLit 2)
  check (!(← match eBeta with | `(expr/defeq -beta| 2 + 1) => pure true | _ => pure false))
    "-beta unexpectedly beta-reduced"
  check (← match eBeta with | `(expr/defeq| 2 + 1) => pure true | _ => pure false)
    "defeq failed to beta-reduce"

  let unusedLet := mkLet `u natTy (mkNatLit 99) (mkNatLit 3)
  check (!(← match unusedLet with | `(expr/defeq -zeta| 3) => pure true | _ => pure false))
    "-zeta unexpectedly dropped unused let"
  check (← match unusedLet with | `(expr/defeq| 3) => pure true | _ => pure false)
    "defeq failed to drop unused let"

  let mkBox := mkApp2 (mkConst ``TestBox.mk) (mkNatLit 4) (mkNatLit 5)
  check (!(← match mkProj ``TestBox 0 mkBox with
    | `(expr/defeq -proj| 4) => pure true | _ => pure false))
    "-proj unexpectedly reduced proj"
  withLocalDeclD `b (mkConst ``TestBox) fun b => do
    let etaB := mkApp2 (mkConst ``TestBox.mk) (mkProj ``TestBox 0 b) (mkProj ``TestBox 1 b)
    check (!(← match etaB with | `(expr/defeq -eta| $b) => pure true | _ => pure false))
      "-eta unexpectedly eta-reduced structure"
    check (← match etaB with | `(expr/defeq| $b) => pure true | _ => pure false)
      "defeq failed to eta-reduce structure"

  -- Consistent leading `let` re-wrapping across `structural +zeta`, `reducible`, `instances`,
  -- and `defeq`.
  let tenPlusTwenty := mkNatAdd (mkNatLit 10) (mkNatLit 20)
  let termLet :=
    mkLet `x natTy tenPlusTwenty <|
      mkLet `unused natTy (mkNatLit 99) <|
        mkNatAdd (mkBVar 1) (mkNatLit 1)
  let expectedTermRewrap := mkLet `x natTy tenPlusTwenty (mkBVar 0)
  let depLetChain :=
    mkLet `a natTy (mkNatLit 1) <|
      mkLet `b natTy (mkNatAdd (mkBVar 0) (mkNatLit 2)) <|
        mkNatAdd (mkNatAdd (mkBVar 0) (mkNatLit 3)) (mkNatLit 1)
  let expectedDepChain :=
    mkLet `a natTy (mkNatLit 1) <|
      mkLet `b natTy (mkNatAdd (mkBVar 0) (mkNatLit 2)) <|
        mkNatAdd (mkBVar 0) (mkNatLit 3)

  let structTerm ← match termLet with
    | `(expr/structural +zeta| ?y + 1) => pure y
    | _ => throwError "structural +zeta termLet failed"
  let redTerm ← match termLet with
    | `(expr/reducible| ?y + 1) => pure y
    | _ => throwError "reducible termLet failed"
  let instTerm ← match termLet with
    | `(expr/instances| ?y + 1) => pure y
    | _ => throwError "instances termLet failed"
  let defeqTerm ← match termLet with
    | `(expr/defeq| ?y + 1) => pure y
    | _ => throwError "defeq termLet failed"
  checkExprEq structTerm expectedTermRewrap "structural +zeta term rewrap"
  checkExprEq redTerm expectedTermRewrap "reducible term rewrap"
  checkExprEq instTerm expectedTermRewrap "instances term rewrap"
  checkExprEq defeqTerm expectedTermRewrap "defeq term rewrap"

  let structDep ← match depLetChain with
    | `(expr/structural +zeta| ?y + 1) => pure y
    | _ => throwError "structural +zeta depLetChain failed"
  let defeqDep ← match depLetChain with
    | `(expr/defeq| ?y + 1) => pure y
    | _ => throwError "defeq depLetChain failed"
  checkExprEq structDep expectedDepChain "structural +zeta dep rewrap"
  checkExprEq defeqDep expectedDepChain "defeq dep rewrap"

  -- Finding #1: nested `let` look-through inside composite arguments across engines + wrapper
  -- unfolding exposing `let`.
  let innerLetArg :=
    mkLet `y natTy (mkNatLit 2) <|
      mkApp (mkConst ``Nat.succ) (mkNatAdd (mkBVar 0) (mkBVar 0))
  let nestedArgTerm := mkApp (mkConst ``testOpaqueDef) innerLetArg
  let expectedInnerRewrap :=
    mkLet `y natTy (mkNatLit 2) (mkNatAdd (mkBVar 0) (mkBVar 0))
  let innerStruct ← match nestedArgTerm with
    | `(expr/structural +zeta| testOpaqueDef (Nat.succ ?x)) => pure x
    | _ => throwError "structural +zeta nested arg let failed"
  let innerRed ← match nestedArgTerm with
    | `(expr/reducible| testOpaqueDef (Nat.succ ?x)) => pure x
    | _ => throwError "reducible nested arg let failed"
  let innerInst ← match nestedArgTerm with
    | `(expr/instances| testOpaqueDef (Nat.succ ?x)) => pure x
    | _ => throwError "instances nested arg let failed"
  let innerDefeq ← match nestedArgTerm with
    | `(expr/defeq| testOpaqueDef (Nat.succ ?x)) => pure x
    | _ => throwError "defeq nested arg let failed"
  checkExprEq innerStruct expectedInnerRewrap "structural +zeta nested arg rewrap"
  checkExprEq innerRed expectedInnerRewrap "reducible nested arg rewrap"
  checkExprEq innerInst expectedInnerRewrap "instances nested arg rewrap"
  checkExprEq innerDefeq expectedInnerRewrap "defeq nested arg rewrap"

  -- Multi-level nested `let`s inside an argument.
  let multiNested :=
    mkApp (mkConst ``testOpaqueDef) <|
      mkLet `y natTy (mkNatLit 2) <|
        mkLet `z natTy (mkNatAdd (mkBVar 0) (mkNatLit 1)) <|
          mkApp (mkConst ``Nat.succ) (mkNatAdd (mkBVar 0) (mkBVar 1))
  let expectedMulti :=
    mkLet `y natTy (mkNatLit 2) <|
      mkLet `z natTy (mkNatAdd (mkBVar 0) (mkNatLit 1)) <|
        mkNatAdd (mkBVar 0) (mkBVar 1)
  let multiDefeq ← match multiNested with
    | `(expr/defeq| testOpaqueDef (Nat.succ ?x)) => pure x
    | _ => throwError "defeq multi-level nested let failed"
  checkExprEq multiDefeq expectedMulti "defeq multi-level nested let rewrap"

  -- Wrapper definition unfolding to expose an inner `let` under `/defeq`.
  let wrappedTarget := mkApp (mkConst ``wrapInnerLet) (mkRawNatLit 2)
  let expectedWrapped :=
    mkLet `y natTy (mkApp2 (mkConst ``Nat.add) (mkRawNatLit 2) (mkRawNatLit 1))
      (mkApp2 (mkConst ``Nat.add) (mkBVar 0) (mkBVar 0)) (nondep := true)
  let wrapDefeq ← match wrappedTarget with
    | `(expr/defeq| Nat.succ ?x) => pure x
    | _ => throwError "defeq wrapper unfolding exposing let failed"
  checkExprEq wrapDefeq expectedWrapped "defeq wrapper-exposed let rewrap"

  -- Context `let`-fvars stay bare (NOT re-wrapped), while nested term `let`s are re-wrapped.
  withLetDecl `cx natTy tenPlusTwenty fun cx => do
    let ctxTarget := mkNatAdd cx (mkNatLit 1)
    let sCx ← match ctxTarget with
      | `(expr/structural +zeta| ?y + 1) => pure y
      | _ => throwError "structural +zeta ctxTarget failed"
    let dCx ← match ctxTarget with
      | `(expr/defeq| ?y + 1) => pure y
      | _ => throwError "defeq ctxTarget failed"
    checkExprEq sCx cx "structural +zeta ctx fvar"
    checkExprEq dCx cx "defeq ctx fvar"

    let nestedCtxTarget :=
      mkApp (mkConst ``testOpaqueDef) (mkApp (mkConst ``Nat.succ) (mkNatAdd cx cx))
    let dNestedCx ← match nestedCtxTarget with
      | `(expr/defeq| testOpaqueDef (Nat.succ ?x)) => pure x
      | _ => throwError "defeq nested ctxTarget failed"
    checkExprEq dNestedCx (mkNatAdd cx cx) "defeq nested ctx fvar must not rewrap"

    let mixedTerm :=
      mkLet `a natTy (mkNatAdd cx (mkNatLit 1)) (mkNatAdd (mkNatAdd (mkBVar 0) cx) (mkNatLit 1))
    let expectedMixed := mkLet `a natTy (mkNatAdd cx (mkNatLit 1)) (mkNatAdd (mkBVar 0) cx)
    let sMix ← match mixedTerm with
      | `(expr/structural +zeta| ?y + 1) => pure y
      | _ => throwError "structural +zeta mixedTerm failed"
    let dMix ← match mixedTerm with
      | `(expr/defeq| ?y + 1) => pure y
      | _ => throwError "defeq mixedTerm failed"
    checkExprEq sMix expectedMixed "structural +zeta mixed rewrap"
    checkExprEq dMix expectedMixed "defeq mixed rewrap"

  -- Finding #5: 100 leading `let`s on failing `/defeq` must make at most 2 `isDefEq` calls.
  let let100Term := mkManyLets 100 (mkApp (mkConst ``Nat.succ) (mkBVar 0))
  resetTraceState
  let hitLet100 ← withOptions (·.setBool `trace.Meta.isDefEq true) do
    match let100Term with
    | `(expr/defeq| Nat.zero) => pure true
    | _ => pure false
  let numDefEqTraces := (← getTraces).size
  resetTraceState
  check (!hitLet100) "100-let term must not match Nat.zero"
  check (numDefEqTraces <= 2) s!"expected <= 2 top-level isDefEq traces, got {numDefEqTraces}"

  -- 0-let constructor miss skips the 2nd zeta fallback `isDefEq` call (`<= 1` trace), while a
  -- non-let surface def whose RHS unfolds to `let` (`mkDefWithLet`) still succeeds via fallback.
  resetTraceState
  let hitZeroMiss ← withOptions (·.setBool `trace.Meta.isDefEq true) do
    match mkApp (mkConst ``Nat.succ) (mkConst ``Nat.zero) with
    | `(expr/defeq| Nat.zero) => pure true
    | _ => pure false
  let numZeroTraces := (← getTraces).size
  resetTraceState
  check (!hitZeroMiss) "Nat.succ Nat.zero must not match Nat.zero"
  check (numZeroTraces <= 1) s!"expected <= 1 isDefEq trace on ctor miss, got {numZeroTraces}"

  let dupVarPat ← ExprPattern.compile {
    levelParams := []
    lam := mkLambda `a .default natTy <| mkApp2 (mkConst ``Nat.add) (mkBVar 0) (mkBVar 0)
    numVars := 1
    namedIdx := #[0]
    firstOrder := #[true]
  }
  let defeqRel ← ({ engine := .defeq } : ExprMatchRel).resolve
  let letTarget := mkApp2 (mkConst ``Nat.add) (mkConst ``mkDefWithLet) (mkRawNatLit 2)
  let some dupRes ← dupVarPat.matchResolved? defeqRel letTarget
    | throwError "expected /defeq fallback to unfold mkDefWithLet"
  check (← isDefEq dupRes[0]! (mkRawNatLit 2)) "matched ?a must be defeq to 2"

  -- Head pin & higher-order pin under `structural +beta` and `structural[+testOpaqueDef]`.
  let addOneLam := mkLambda `z .default natTy (mkNatAdd (mkBVar 0) (mkNatLit 1))
  let headBetaHit ← match mkNatAdd (mkNatLit 42) (mkNatLit 1) with
    | `(expr/structural +beta| $addOneLam ?x) => pure (some x)
    | _ => pure none
  check (headBetaHit == some (mkNatLit 42)) "head pin +beta failed"

  let fnOpaque := mkConst ``testOpaqueDef
  let headConstHit ← match mkNatLit 8 with
    | `(expr/structural[+testOpaqueDef]| $fnOpaque ?x) => pure (some x)
    | _ => pure none
  check (headConstHit == some (mkNatLit 8)) "head pin +testOpaqueDef failed"

  let hoEtaTarget :=
    mkLambda `w .default natTy (mkNatAdd (mkNatAdd (mkBVar 0) (mkNatLit 1)) (mkNatLit 0))
  let hoPinHit ← match hoEtaTarget with
    | `(expr/structural +beta| fun z => $addOneLam z + 0) => pure true
    | _ => pure false
  check hoPinHit "higher-order pin under +beta failed"

#guard_msgs in
#eval show MetaM Unit from testEnginesFlagsAndRewrap

/-! ## 7. `ResolvedExprMatchRel`, per-site `[+simp]` cache, precedence, local validation -/

private def matchWithDynSiteCache (e : Expr) : MetaM Bool := do
  let simpRel : ExprMatchRel := {
    engine := .structural
    items := #[{ positive := true, declName := `simp, isSimpSet := true }]
  }
  let rel ← simpRel.resolve (siteId := `ExprPatternTest.dynSiteCache)
  let patApp ← ExprPattern.compile {
    levelParams := []
    lam         := mkApp (mkConst ``cacheDynSimpDef) (mkNatLit 5)
    numVars     := 0
    namedIdx    := #[]
    firstOrder  := #[]
  }
  return (← patApp.matchResolved? rel e).isSome

#guard_msgs in
#eval show MetaM Unit from do
  -- Populates and reuses cached `siteId` while `cacheDynSimpDef` has `@[simp]`.
  check (← matchWithDynSiteCache (mkNatLit 5)) "expected cached [+simp] hit before -simp"
  check (← matchWithDynSiteCache (mkNatLit 5)) "expected cached [+simp] hit on reuse"

attribute [-simp] cacheDynSimpDef

#guard_msgs in
#eval show MetaM Unit from do
  -- Reusing the exact same `siteId` after `attribute [-simp]` must refresh simp state in `O(1)`.
  check (!(← matchWithDynSiteCache (mkNatLit 5)))
    "cached site must reflect `attribute [-simp]` update immediately"

private def testItemsAndValidation : MetaM Unit := do
  -- Compiled `ExprQuot` `[+simp]` site (`matchSiteOrElse`) & erased simp behavior.
  let hitSimpCodegen ← match mkNatLit 5 with
    | `(expr/structural[+simp]| testSimpDef 5) => pure true
    | _ => pure false
  check hitSimpCodegen "compiled [+simp] site failed to unfold testSimpDef"
  let hitErasedCodegen ← match mkNatLit 5 with
    | `(expr/structural[+simp]| testErasedSimpDef 5) => pure true
    | _ => pure false
  check (!hitErasedCodegen) "compiled [+simp] site unfolded erased testErasedSimpDef"

  -- `matchResolvedPins?` / `matchResolvedOrElse` reuse without re-resolving items.
  let pat ← ExprPattern.compile {
    levelParams := []
    lam := mkLambda `p .default (mkConst ``Nat) (mkApp (mkConst ``testSimpDef) (mkBVar 0))
    numVars := 1
    namedIdx := #[]
    firstOrder := #[true]
  }
  let simpRel : ExprMatchRel := {
    engine := .structural
    items := #[{ positive := true, declName := `simp, isSimpSet := true }]
  }
  let resolvedSimp ← simpRel.resolveStatic
  let some xs ← pat.matchResolvedPins? resolvedSimp #[0] #[mkNatLit 5] (mkNatLit 5)
    | throwError "expected resolved pin match"
  check xs.isEmpty "expected empty named bindings"
  let cpsRes ← pat.matchResolvedOrElse resolvedSimp #[0] #[mkNatLit 5] (mkNatLit 5)
    (fun _ => pure true) (fun _ => pure false)
  check cpsRes "expected matchResolvedOrElse success"

  -- Precedence & erased simp theorem behavior:
  let erasedPat ← ExprPattern.compile {
    levelParams := []
    lam := mkLambda `p .default (mkConst ``Nat) (mkApp (mkConst ``testErasedSimpDef) (mkBVar 0))
    numVars := 1
    namedIdx := #[]
    firstOrder := #[true]
  }
  check (← erasedPat.matchResolvedPins? resolvedSimp #[0] #[mkNatLit 5] (mkNatLit 5)).isNone
    "erased simp theorem must not unfold"
  let simpOverrideRel : ExprMatchRel := {
    engine := .structural
    items := #[
      { positive := true, declName := `simp, isSimpSet := true },
      { positive := false, declName := ``testSimpDef, isSimpSet := false }
    ]
  }
  let resolvedOverride ← simpOverrideRel.resolveStatic
  check (← pat.matchResolvedPins? resolvedOverride #[0] #[mkNatLit 5] (mkNatLit 5)).isNone
    "[+simp, -testSimpDef] must suppress testSimpDef"

  -- Validation errors via `resolveStatic` and `withLocalItems`:
  checkErrContains (ExprMatchRel.resolveStatic {
    engine := .structural
    items := #[{ positive := true, declName := `nonexistentSimpAttr, isSimpSet := true }]
  }) "unknown simp attribute"

  checkErrContains (ExprMatchRel.resolveStatic {
    engine := .structural
    items := #[{ positive := true, declName := `Nonexistent.Const }]
  }) "unknown constant"

  checkErrContains (ExprMatchRel.resolveStatic {
    engine := .structural
    items := #[{ positive := false, declName := ``testOpaqueDef }]
  }) "does not unfold"

  checkErrContains (ExprMatchRel.resolveStatic {
    engine := .structural
    items := #[{ positive := false, declName := `simp, isSimpSet := true }]
  }) "does not unfold any simp-set definitions"

  let baseStruct ← ({ engine := .structural } : ExprMatchRel).resolveStatic
  let baseDefeq ← ({ engine := .defeq } : ExprMatchRel).resolveStatic
  let baseDefeqNoZeta ← ({ engine := .defeq, flags := { zeta := some false } } :
    ExprMatchRel).resolveStatic

  checkErrContains (baseStruct.withLocalItems #[(true, mkNatLit 0)])
    "must evaluate to a free variable"

  let staleFV : Expr := mkFVar ⟨`_stale_local_999⟩
  checkErrContains (baseStruct.withLocalItems #[(true, staleFV)]) "not in the local context"

  withLocalDeclD `c (mkConst ``Nat) fun c =>
    withLetDecl `h (mkConst ``Nat) (mkNatLit 1) (nondep := true) fun h =>
    withLetDecl `v (mkConst ``Nat) (mkNatLit 2) (nondep := false) fun v => do
      checkErrContains (baseStruct.withLocalItems #[(true, c)])
        "not a `let`-bound local definition"
      checkErrContains (baseStruct.withLocalItems #[(true, h)])
        "not a `let`-bound local definition"
      checkErrContains (baseStruct.withLocalItems #[(false, v)]) "not unfolded by default"
      checkErrContains (baseDefeqNoZeta.withLocalItems #[(false, v)]) "not unfolded by default"
      let _ ← baseDefeq.withLocalItems #[(false, v)]
      let cancelled ← baseStruct.withLocalItems #[(true, v), (false, v)]
      check (cancelled.posFVars.isEmpty && cancelled.negFVars == #[v.fvarId!])
        "expected cancelled +v/-v to leave negFVars = #[v]"

#guard_msgs in
#eval show MetaM Unit from testItemsAndValidation

/-! ## 8. `ExprContext.fill` & Spec §5 sources (`localHyp*`, `subterms`, `matchDiscriminants`) -/

private def realNestedMatch (x : Nat) : Nat :=
  (match Nat.add (nat_lit 1) (nat_lit 2) with
   | 0 => fun (k : Nat) => k + x
   | n + 1 => fun (k : Nat) =>
     match Nat.add n (nat_lit 10), Nat.add (nat_lit 3) (nat_lit 4) with
     | 0, _ => k
     | _, m => m + k) (Nat.add (nat_lit 5) (nat_lit 6))

private def realDupDiscrs (x : Nat) : Nat :=
  Nat.add
    (match Nat.add (nat_lit 1) (nat_lit 2) with
     | 0 => x
     | n + 1 => n + x)
    (match Nat.add (nat_lit 1) (nat_lit 2) with
     | 0 => x + 1
     | n + 1 => n + x + 2)

private def realNatCases : Nat :=
  Nat.casesOn (Nat.add (nat_lit 8) (nat_lit 9)) (nat_lit 0) (fun n => n)

private def realNatCasesZero : Nat :=
  Nat.casesOn (nat_lit 0) (nat_lit 0) (fun n => n)

private def realPolyCases : Nat :=
  @PolyVec.casesOn Nat (fun _ _ => Nat) (nat_lit 0) (@PolyVec.nil Nat) (nat_lit 0)
    (fun _ _ => 1)

private def testContextAndSources : MetaM Unit := do
  -- `localHypTypes` & `localHypDecls`:
  withLocalDecl `impl BinderInfo.default (mkConst ``Nat) (kind := .implDetail) fun _impl =>
  withLocalDeclD `h1 (mkConst ``Nat) fun h1 =>
  withLetDecl `hv (mkConst ``Nat) (mkNatLit 10) (nondep := true) fun hv =>
  withLetDecl `lv (mkConst ``Nat) (mkNatLit 20) (nondep := false) fun lv => do
    let mTy ← mkFreshTypeMVar
    mTy.mvarId!.assign (mkConst ``Bool)
    withLocalDeclD `h2 mTy fun h2 => do
      let hyps ← localHypTypes
      let hypsRev ← localHypTypes (reverse := true)
      let hypsEx ← localHypTypes (except := [h1, hv])
      let expectedNames := #[h1, hv, lv, h2]
      check (hyps.map (·.1) == expectedNames) "localHypTypes oldest-first order mismatch"
      checkExprEq hyps[3]!.2 (mkConst ``Bool) "localHypTypes instantiated mvar type"
      check (hypsRev.map (·.1) == expectedNames.reverse) "localHypTypes reverse mismatch"
      check (hypsEx.map (·.1) == #[lv, h2]) "localHypTypes except mismatch"

      let decls ← localHypDecls
      check (decls.size == 4) "localHypDecls count mismatch"
      check decls[0]!.2.2.isNone "cdecl must have val? = none"
      check decls[1]!.2.2.isNone "`have` (`nondep := true`) must have val? = none"
      check (decls[2]!.2.2 == some (mkNatLit 20)) "`let` (`nondep := false`) val? mismatch"
      checkExprEq decls[3]!.2.1 (mkConst ``Bool) "localHypDecls instantiated mvar type"

  -- `subterms` & `ExprContext.fill` on closed subterms under binders and `mdata`:
  let mWrapped := mkMData {} (mkNatAdd (mkNatLit 1) (mkNatLit 2))
  let bodyWithBinder :=
    mkLambda `x BinderInfo.default (mkApp (mkConst ``List [0]) (mkConst ``Nat)) <|
      mkNatAdd (mkBVar 0) mWrapped
  let subs := (subterms bodyWithBinder).toArray
  checkExprEq subs[0]!.1 bodyWithBinder "first closed subterm must be root"
  check (subs.any (·.1 == mkApp (mkConst ``List [0]) (mkConst ``Nat)))
    "binder domain `List Nat` missing"
  check (subs.any (·.1 == mkConst ``Nat)) "binder nested domain `Nat` missing"
  check (subs.all fun (sub, _) => !sub.hasLooseBVars) "open subterm unexpectedly emitted"
  check ((subs.filter (·.1 == mkNatAdd (mkNatLit 1) (mkNatLit 2))).size == 1)
    "mdata child duplicated or missing"
  let some (subAdd, ctxAdd) := subs.find? (·.1 == mkNatAdd (mkNatLit 1) (mkNatLit 2))
    | throwError "expected `1 + 2` subterm"
  checkExprEq (ctxAdd.fill subAdd) bodyWithBinder "ExprContext.fill mdata round-trip"
  let expectedReplaced :=
    mkLambda `x BinderInfo.default (mkApp (mkConst ``List [0]) (mkConst ``Nat)) <|
      mkNatAdd (mkBVar 0) (mkMData {} (mkNatLit 99))
  checkExprEq (ctxAdd.fill (mkNatLit 99)) expectedReplaced "ExprContext.fill keeps mdata"

  -- `ExprContext.fill` across `proj`, `let`, `forallE`:
  let complex :=
    mkForall `a .default (mkConst ``Nat) <|
      mkLet `t (mkConst ``Nat) (mkNatAdd (mkNatLit 3) (mkNatLit 4))
        (mkProj ``TestBox 0 (mkApp2 (mkConst ``TestBox.mk) (mkBVar 1) (mkNatLit 5)))
  for (sub, ctx) in subterms complex do
    checkExprEq (ctx.fill sub) complex "complex ExprContext.fill round-trip"
  let some (_, ctx3) := (subterms complex).toArray.find? (·.1 == mkNatLit 3)
    | throwError "expected 3 subterm"
  check (ctx3.fill (mkNatLit 30) != complex) "replacing 3 inside let value should change term"

  -- Finding #4: 22-level `e + e` shared DAG dedup & genuine lazy early `break`.
  let mut dag := mkRawNatLit 1
  for _ in *...22 do
    dag := mkApp2 (mkConst ``Nat.add) dag dag
  let dagSubs := (subterms dag).toArray
  check (dagSubs.size < 40)
    s!"expected < 40 deduplicated subterms on 22-level DAG, got {dagSubs.size}"
  for (s, c) in dagSubs do
    checkExprEq (c.fill s) dag "22-level DAG ExprContext.fill round-trip"

  -- Without `dedup`, `subterms` on the 22-level DAG has >100M paths; early `break` stops at 3.
  let mut lazyCount := 0
  for _ in subterms dag (dedup := false) do
    lazyCount := lazyCount + 1
    if lazyCount == 3 then
      break
  check (lazyCount == 3) s!"expected early break after 3 nodes, got {lazyCount}"

  -- Finding #4 (`dedup := false` vs `dedup := true` on `x + x` & `includeAppPrefixes` on `f a b`).
  withLocalDeclD `x (mkConst ``Nat) fun x =>
  withLocalDeclD `f (mkConst ``Nat.add) fun f =>
  withLocalDeclD `a (mkConst ``Nat) fun a =>
  withLocalDeclD `b (mkConst ``Nat) fun b => do
    let xx := mkApp2 (mkConst ``Nat.add) x x
    let xxDedup := ((subterms xx).toArray.filter (·.1 == x))
    let xxAll := ((subterms xx (dedup := false)).toArray.filter (·.1 == x))
    check (xxDedup.size == 1) s!"expected 1 dedup occurrence of x in x+x, got {xxDedup.size}"
    check (xxAll.size == 2) s!"expected 2 non-dedup occurrences of x in x+x, got {xxAll.size}"
    checkExprEq (xxDedup[0]!.2.fill (mkNatLit 99)) (mkApp2 (mkConst ``Nat.add) (mkNatLit 99) x)
      "dedup must yield first occurrence context"
    checkExprEq (xxAll[0]!.2.fill (mkNatLit 99)) (mkApp2 (mkConst ``Nat.add) (mkNatLit 99) x)
      "non-dedup first x replacement"
    checkExprEq (xxAll[1]!.2.fill (mkNatLit 99)) (mkApp2 (mkConst ``Nat.add) x (mkNatLit 99))
      "non-dedup second x replacement"

    let fab := mkApp2 f a b
    let fa := mkApp f a
    let noPrefixes := (subterms fab).toArray
    let withPrefixes := (subterms fab (includeAppPrefixes := true)).toArray
    check (noPrefixes.map (·.1) == #[fab, f, a, b]) "includeAppPrefixes := false node list mismatch"
    check (withPrefixes.map (·.1) == #[fab, fa, f, a, b])
      "includeAppPrefixes := true node list mismatch"
    for (s, c) in noPrefixes do
      checkExprEq (c.fill s) fab "spine ExprContext.fill round-trip"
    checkExprEq (noPrefixes[1]!.2.fill (mkNatLit 99)) (mkApp2 (mkNatLit 99) a b)
      "spine head replacement"
    checkExprEq (noPrefixes[2]!.2.fill (mkNatLit 99)) (mkApp2 f (mkNatLit 99) b)
      "spine arg 0 replacement"
    checkExprEq (noPrefixes[3]!.2.fill (mkNatLit 99)) (mkApp2 f a (mkNatLit 99))
      "spine arg 1 replacement"

  -- `matchDiscriminants` on real elaborated `match` (nested `match`, lazy `ForIn`, `dedup`).
  let innerMatchExpr := (← getConstInfo ``realNestedMatch).value!
  let discrs ← (matchDiscriminants innerMatchExpr).toArray
  let natAdd12 := mkApp2 (mkConst ``Nat.add) (mkRawNatLit 1) (mkRawNatLit 2)
  let natAdd34 := mkApp2 (mkConst ``Nat.add) (mkRawNatLit 3) (mkRawNatLit 4)
  check ((discrs.filter (·.1 == natAdd12)).size == 1) "outer discriminant duplicated"
  check (discrs.all (!·.1.hasLooseBVars)) "open discriminant emitted"
  check ((discrs.filter (·.1 == natAdd34)).size == 1) "inner closed discriminant missing"
  check (discrs.size == 2) s!"expected 2 discriminants, got {discrs.size}"
  checkExprEq (discrs[0]!.2.fill discrs[0]!.1) innerMatchExpr "discriminant round-trip"
  let replacedDiscr := discrs[0]!.2.fill (mkNatLit 77)
  let discrsAfter ← (matchDiscriminants replacedDiscr).toArray
  checkExprEq discrsAfter[0]!.1 (mkNatLit 77) "replaced outer discriminant mismatch"

  let mut discrBreakCount := 0
  for _ in matchDiscriminants innerMatchExpr do
    discrBreakCount := discrBreakCount + 1
    break
  check (discrBreakCount == 1) "matchDiscriminants early break failed"

  let dupDiscrExpr := (← getConstInfo ``realDupDiscrs).value!
  let dupDedup ← (matchDiscriminants dupDiscrExpr).toArray
  let dupAll ← (matchDiscriminants dupDiscrExpr (dedup := false)).toArray
  check (dupDedup.size == 1) s!"expected 1 dedup discriminant, got {dupDedup.size}"
  check (dupAll.size == 2) s!"expected 2 non-dedup discriminants, got {dupAll.size}"
  check (dupAll[0]!.2.fill (mkRawNatLit 99) != dupAll[1]!.2.fill (mkRawNatLit 99))
    "non-dedup duplicate discriminants must have distinct ExprContexts"

  -- `alsoCasesOn := false` ignores `casesOn`, `alsoCasesOn := true` extracts it.
  let casesTerm := (← getConstInfo ``realNatCases).value!
  let casesTermZero := (← getConstInfo ``realNatCasesZero).value!
  check (← (matchDiscriminants casesTerm (alsoCasesOn := false)).toArray).isEmpty
    "alsoCasesOn := false must ignore casesOn"
  let casesDiscrs ← (matchDiscriminants casesTerm (alsoCasesOn := true)).toArray
  check (casesDiscrs.size == 1) "expected 1 casesOn discriminant"
  checkExprEq casesDiscrs[0]!.1 (mkApp2 (mkConst ``Nat.add) (mkRawNatLit 8) (mkRawNatLit 9))
    "casesOn major arg"
  checkExprEq (casesDiscrs[0]!.2.fill (mkRawNatLit 0)) casesTermZero "casesOn replacement"

  let indexedCases := (← getConstInfo ``realPolyCases).value!
  let indexedDiscrs ← (matchDiscriminants indexedCases (alsoCasesOn := true)).toArray
  check (indexedDiscrs.size == 2) "expected 2 indexed casesOn discriminants"
  checkExprEq indexedDiscrs[0]!.1 (mkRawNatLit 0) "indexed casesOn index discriminant"
  checkExprEq (indexedDiscrs[1]!.2.fill indexedDiscrs[1]!.1) indexedCases
    "indexed casesOn major round-trip"

#guard_msgs in
#eval show MetaM Unit from testContextAndSources

#guard_msgs in
#eval show MetaM Unit from do
  check (← allowMinusAfterPlusMerged (mkApp (mkConst ``sampleDef) (mkNatLit 0)))
    "merged [+sampleDef, -sampleDef] should match sampleDef 0 literally"

/-! ## Compact DAG Serialization & `PatHeadGuard` Fast-Reject Tests -/

private def exprExactEq : Expr → Expr → Bool
  | .bvar i₁, .bvar i₂ => i₁ == i₂
  | .sort u₁, .sort u₂ => u₁ == u₂
  | .const n₁ us₁, .const n₂ us₂ => n₁ == n₂ && us₁ == us₂
  | .app f₁ a₁, .app f₂ a₂ => exprExactEq f₁ f₂ && exprExactEq a₁ a₂
  | .lam n₁ t₁ b₁ bi₁, .lam n₂ t₂ b₂ bi₂ =>
    n₁ == n₂ && bi₁ == bi₂ && exprExactEq t₁ t₂ && exprExactEq b₁ b₂
  | .forallE n₁ t₁ b₁ bi₁, .forallE n₂ t₂ b₂ bi₂ =>
    n₁ == n₂ && bi₁ == bi₂ && exprExactEq t₁ t₂ && exprExactEq b₁ b₂
  | .letE n₁ t₁ v₁ b₁ nd₁, .letE n₂ t₂ v₂ b₂ nd₂ =>
    n₁ == n₂ && nd₁ == nd₂ && exprExactEq t₁ t₂ && exprExactEq v₁ v₂ && exprExactEq b₁ b₂
  | .lit l₁, .lit l₂ => l₁ == l₂
  | .proj s₁ i₁ b₁, .proj s₂ i₂ b₂ => s₁ == s₂ && i₁ == i₂ && exprExactEq b₁ b₂
  | _, _ => false

private def testDagSerializationRoundTrip : MetaM Unit := do
  let uLvl := Level.param `u
  let vLvl := Level.param `v
  let complexLvl := Level.imax (.succ uLvl) (.max .zero vLvl)
  let bigNat : Nat := (2 ^ 100) + 1234567890123456789
  let uniStr := "λ ∀ α — β 🚀"
  let uniName := Name.str (.num `Root 42) uniStr
  let proofTerm := mkConst ``True.intro
  let body :=
    mkLambda `a .default (mkSort complexLvl) <|
    mkLambda `b .implicit (mkConst ``Nat) <|
    mkForall `c .strictImplicit (mkConst ``Nat) <|
    mkForall `d .instImplicit (mkApp (mkConst ``Inhabited [uLvl]) (mkSort vLvl)) <|
    mkLet `x (mkConst ``Nat) (mkLit (.natVal bigNat)) (nondep := false) <|
    mkLet `h (mkConst ``String) (mkLit (.strVal uniStr)) (nondep := true) <|
    mkAppN (mkConst uniName [complexLvl]) #[
      mkProj `Prod 0 (mkBVar 5),
      proofTerm,
      mkBVar 0
    ]
  let pat0 : ExprPattern := {
    levelParams := [`u, `v]
    lam         := body
    numVars     := 1
    namedIdx    := #[0]
    firstOrder  := #[true]
  }
  let pat ← pat0.compile
  let encoded ← match pat.encode with
    | .ok s    => pure s
    | .error e => throwError "pat.encode failed: {e}"
  check (encoded.toList.all fun c => c.toNat >= 48 && c.toNat <= 111)
    "encoded pattern string must only use printable ASCII `'0'..'o'`"
  let decoded ← match ExprPattern.decodeExcept encoded with
    | .ok d    => pure d
    | .error e => throwError "pat.decode failed: {e}"
  check (decoded.levelParams == pat.levelParams) "levelParams round-trip mismatch"
  check (exprExactEq decoded.lam pat.lam) "pattern lam strict round-trip mismatch"
  check (decoded.numVars == pat.numVars) "numVars round-trip mismatch"
  check (decoded.namedIdx == pat.namedIdx) "namedIdx round-trip mismatch"
  check (decoded.firstOrder == pat.firstOrder) "firstOrder round-trip mismatch"
  check (decoded.captureVars == pat.captureVars) "captureVars round-trip mismatch"
  check (decoded.precomputed == pat.precomputed) "precomputed round-trip mismatch"
  check (decoded.headGuard == pat.headGuard) "headGuard round-trip mismatch"
  check (decoded.closedProofs.contains proofTerm) "closedProofs round-trip missing True.intro"
  check (decoded.patLevelNodes.size == pat.patLevelNodes.size) "patLevelNodes round-trip mismatch"

  let tmpl : ExprTemplate := {
    levelParams := [`u, `v]
    lam         := body
    varKinds    := #[.splice 0, .hole none, .hole (some uniName), .tc, .infer]
  }
  let tmplEnc ← match tmpl.encode with
    | .ok s    => pure s
    | .error e => throwError "tmpl.encode failed: {e}"
  let tmplDec ← match ExprTemplate.decodeExcept tmplEnc with
    | .ok d    => pure d
    | .error e => throwError "tmpl.decode failed: {e}"
  check (tmplDec.levelParams == tmpl.levelParams) "tmpl levelParams round-trip mismatch"
  check (exprExactEq tmplDec.lam tmpl.lam) "tmpl lam strict round-trip mismatch"
  check (tmplDec.varKinds == tmpl.varKinds) "tmpl varKinds round-trip mismatch"

  -- Corrupt payloads must fail cleanly in `decodeExcept`.
  check (ExprPattern.decodeExcept "" matches .error _) "empty pattern blob must fail"
  check (ExprPattern.decodeExcept "!" matches .error _) "non-ASCII character must fail"
  check (ExprTemplate.decodeExcept encoded matches .error _) "version mismatch must fail"

private def testPatHeadGuards : MetaM Unit := do
  -- 1. `.const` guard on `Nat.add ?x _`, including assigned head `.mvar` scrutinee.
  let addPat ← ExprPattern.compile {
    levelParams := []
    lam         := mkLambda `x .default (mkConst ``Nat)
      (mkLambda `w .default (mkConst ``Nat)
        (mkApp2 (mkConst ``Nat.add) (mkBVar 1) (mkBVar 0)))
    numVars     := 2
    namedIdx    := #[0]
    firstOrder  := #[true]
  }
  check (addPat.headGuard == .const ``Nat.add 2)
    s!"expected const Nat.add 2 guard, got {repr addPat.headGuard}"
  let add12 := mkApp2 (mkConst ``Nat.add) (mkNatLit 1) (mkNatLit 2)
  let mul12 := mkApp2 (mkConst ``Nat.mul) (mkNatLit 1) (mkNatLit 2)
  check ((← addPat.match? {} mul12) == none) "mul12 should miss Nat.add"
  let mv ← mkFreshExprMVar (mkConst ``Nat)
  mv.mvarId!.assign add12
  let some #[hit] ← addPat.match? {} mv
    | throwError "assigned mvar scrutinee must NOT be falsely rejected by headGuard"
  checkExprEq hit (mkNatLit 1) "assigned mvar match capture mismatch"

  -- 2. `.pinApp` guard on `($f : Nat → Nat) ?x` (const pin, lambda pin, assigned mvar pin).
  let natToNat := mkForall `n .default (mkConst ``Nat) (mkConst ``Nat)
  let pinAppPat ← ExprPattern.compile {
    levelParams := []
    lam         := mkLambda `f .default natToNat
      (mkLambda `x .default (mkConst ``Nat) (mkApp (mkBVar 1) (mkBVar 0)))
    numVars     := 2
    namedIdx    := #[1]
    firstOrder  := #[true, true]
  }
  check (pinAppPat.headGuard == .pinApp 0 1)
    s!"expected pinApp 0 1 guard, got {repr pinAppPat.headGuard}"
  let resolvedStruct ← ({} : ExprMatchRel).resolveStatic
  let succ3 := mkApp (mkConst ``Nat.succ) (mkNatLit 3)
  let some #[capSucc] ← pinAppPat.matchResolvedPins? resolvedStruct #[0]
      #[mkConst ``Nat.succ] succ3
    | throwError "pinApp with Nat.succ pin should match Nat.succ 3"
  checkExprEq capSucc (mkNatLit 3) "pinApp capture mismatch"
  check ((← pinAppPat.matchResolvedPins? resolvedStruct #[0]
      #[mkConst ``Nat.pred] succ3) == none) "pinApp with Nat.pred pin should reject Nat.succ 3"
  let idLam := mkLambda `n .default (mkConst ``Nat) (mkBVar 0)
  let idApp3 := mkApp idLam (mkNatLit 3)
  let some #[capLam] ← pinAppPat.matchResolvedPins? resolvedStruct #[0] #[idLam] idApp3
    | throwError "pinApp with lambda pin should match lambda app"
  checkExprEq capLam (mkNatLit 3) "pinApp lambda capture mismatch"
  let pinMV ← mkFreshExprMVar natToNat
  pinMV.mvarId!.assign (mkConst ``Nat.succ)
  let some #[capMV] ← pinAppPat.matchResolvedPins? resolvedStruct #[0] #[pinMV] succ3
    | throwError "pinApp with assigned mvar pin must NOT be falsely rejected"
  checkExprEq capMV (mkNatLit 3) "pinApp mvar pin capture mismatch"

  -- 3. Closed `Prop` proof pattern keeps `headGuard = .any` and matches distinct proofs.
  let proofRootPat ← ExprPattern.compile {
    levelParams := []
    lam         := mkConst ``True.intro
    numVars     := 0
    namedIdx    := #[]
    firstOrder  := #[]
  }
  check (proofRootPat.headGuard == .any)
    s!"closed proof root must have .any headGuard, got {repr proofRootPat.headGuard}"
  withLocalDeclD `h (mkConst ``True) fun h => do
    check (← proofRootPat.match? {} h).isSome
      "closed Prop proof pattern must not be rejected against distinct Prop proof"

#guard_msgs in
#eval show MetaM Unit from do
  testDagSerializationRoundTrip
  testPatHeadGuards

end ExprPatternTest
