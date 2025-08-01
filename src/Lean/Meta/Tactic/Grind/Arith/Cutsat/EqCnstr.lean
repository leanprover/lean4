/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Tactic.Grind.Simp
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Var
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.DvdCnstr
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.LeCnstr
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.ToInt
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.CommRing

public section

namespace Lean.Meta.Grind.Arith.Cutsat

private def _root_.Int.Linear.Poly.substVar (p : Poly) : GoalM (Option (Var × EqCnstr × Poly)) := do
  let some (a, x, c) ← p.findVarToSubst | return none
  let b := c.p.coeff x
  let p' := p.mul (-b) |>.combine (c.p.mul a)
  trace[grind.debug.cutsat.subst] "{← p.pp}, {a}, {← getVar x}, {← c.pp}, {b}, {← p'.pp}"
  return some (x, c, p')

def EqCnstr.norm (c : EqCnstr) : EqCnstr :=
  if c.p.isSorted then
    c
  else
    { p := c.p.norm, h := .norm c }

def DiseqCnstr.norm (c : DiseqCnstr) : DiseqCnstr :=
  if c.p.isSorted then
    c
  else
    { p := c.p.norm, h := .norm c }

/--
Given an equation `c₁` containing the monomial `a*x`, and a disequality constraint `c₂`
containing the monomial `b*x`, eliminate `x` by applying substitution.
-/
def DiseqCnstr.applyEq (a : Int) (x : Var) (c₁ : EqCnstr) (b : Int) (c₂ : DiseqCnstr) : GoalM DiseqCnstr := do
  let p := c₁.p
  let q := c₂.p
  let p := p.mul b |>.combine (q.mul (-a))
  trace[grind.debug.cutsat.subst] "{← getVar x}, {← c₁.pp}, {← c₂.pp}"
  return { p, h := .subst x c₁ c₂ }

partial def DiseqCnstr.applySubsts (c : DiseqCnstr) : GoalM DiseqCnstr := withIncRecDepth do
  let some (x, c₁, p) ← c.p.substVar | return c
  trace[grind.debug.cutsat.subst] "{← getVar x}, {← c.pp}, {← c₁.pp}"
  applySubsts { p, h := .subst x c₁ c }

/--
Given a disequality `c`, tries to find an inequality to be refined using
`p ≤ 0 → p ≠ 0 → p + 1 ≤ 0`
-/
private def DiseqCnstr.findLe (c : DiseqCnstr) : GoalM Bool := do
  let .add _ x _ := c.p | c.throwUnexpected
  let s ← get'
  let go (atLower : Bool) : GoalM Bool := do
    let cs' := if atLower then s.lowers[x]! else s.uppers[x]!
    for c' in cs' do
      if c.p == c'.p || c.p.isNegEq c'.p then
        c'.erase
        { p := c'.p.addConst 1, h := .ofLeDiseq c' c : LeCnstr }.assert
        return true
    return false
  go true <||> go false

def DiseqCnstr.assert (c : DiseqCnstr) : GoalM Unit := do
  if (← inconsistent) then return ()
  trace[grind.cutsat.assert] "{← c.pp}"
  let c ← c.norm.applySubsts
  if c.p.isUnsatDiseq then
    trace[grind.cutsat.assert.unsat] "{← c.pp}"
    setInconsistent (.diseq c)
    return ()
  if c.isTrivial then
    trace[grind.cutsat.assert.trivial] "{← c.pp}"
    return ()
  let k := c.p.gcdCoeffs c.p.getConst
  let c := if k == 1 then
    c
  else
    { p := c.p.div k, h := .divCoeffs c }
  if (← c.findLe) then
    return ()
  let .add _ x _ := c.p | c.throwUnexpected
  c.p.updateOccs
  trace[grind.cutsat.assert.store] "{← c.pp}"
  modify' fun s => { s with diseqs := s.diseqs.modify x (·.push c) }
  if (← c.satisfied) == .false then
    resetAssignmentFrom x

/--
Selects the variable in the given linear polynomial whose coefficient has the smallest absolute value.
-/
def _root_.Int.Linear.Poly.pickVarToElim? (p : Poly) : Option (Int × Var) :=
  match p with
  | .num _ => none
  | .add k x p => go k x p
where
  go (k : Int) (x : Var) (p : Poly) : Int × Var :=
    if k == 1 || k == -1 then
      (k, x)
    else match p with
      | .num _ => (k, x)
      | .add k' x' p =>
        if k'.natAbs < k.natAbs then
          go k' x' p
        else
          go k x p

partial def EqCnstr.applySubsts (c : EqCnstr) : GoalM EqCnstr := withIncRecDepth do
  let some (x, c₁, p) ← c.p.substVar | return c
  trace[grind.debug.cutsat.subst] "{← getVar x}, {← c.pp}, {← c₁.pp}"
  applySubsts { p, h := .subst x c₁ c : EqCnstr }

private def updateDvdCnstr (a : Int) (x : Var) (c : EqCnstr) (y : Var) : GoalM Unit := do
  let some c' := (← get').dvds[y]! | return ()
  let b := c'.p.coeff x
  if b == 0 then return ()
  modify' fun s => { s with dvds := s.dvds.set y none }
  let c' ← c'.applyEq a x c b
  c'.assert

private def splitLeCnstrs (x : Var) (cs : PArray LeCnstr) : PArray LeCnstr × Array (Int × LeCnstr) :=
  split cs fun c => c.p.coeff x

/--
Given an equation `c₁` containing `a*x`, eliminate `x` from the inequalities in `todo`.
`todo` contains pairs of the form `(b, c₂)` where `b` is the coefficient of `x` in `c₂`.
-/
private def updateLeCnstrs (a : Int) (x : Var) (c₁ : EqCnstr) (todo : Array (Int × LeCnstr)) : GoalM Unit := do
  for (b, c₂) in todo do
    let c₂ ← c₂.applyEq a x c₁ b
    c₂.assert
    if (← inconsistent) then return ()

/--
Given an equation `c₁` containing `a*x`, eliminate `x` from lower bound inequalities of `y`.
-/
private def updateLowers (a : Int) (x : Var) (c : EqCnstr) (y : Var) : GoalM Unit := do
  if (← inconsistent) then return ()
  let (lowers', todo) := splitLeCnstrs x (← get').lowers[y]!
  modify' fun s => { s with lowers := s.lowers.set y lowers' }
  updateLeCnstrs a x c todo

/--
Given an equation `c₁` containing `a*x`, eliminate `x` from upper bound inequalities of `y`.
-/
private def updateUppers (a : Int) (x : Var) (c : EqCnstr) (y : Var) : GoalM Unit := do
  if (← inconsistent) then return ()
  let (uppers', todo) := splitLeCnstrs x (← get').uppers[y]!
  modify' fun s => { s with uppers := s.uppers.set y uppers' }
  updateLeCnstrs a x c todo

private def splitDiseqs (x : Var) (cs : PArray DiseqCnstr) : PArray DiseqCnstr × Array (Int × DiseqCnstr) :=
  split cs fun c => c.p.coeff x

private def updateDiseqs (a : Int) (x : Var) (c : EqCnstr) (y : Var) : GoalM Unit := do
  if (← inconsistent) then return ()
  let (diseqs', todo) := splitDiseqs x (← get').diseqs[y]!
  modify' fun s => { s with diseqs := s.diseqs.set y diseqs' }
  for (b, c₂) in todo do
    let c₂ ← c₂.applyEq a x c b
    c₂.assert
    if (← inconsistent) then return ()

private def updateOccsAt (k : Int) (x : Var) (c : EqCnstr) (y : Var) : GoalM Unit := do
  updateDvdCnstr k x c y
  updateLowers k x c y
  updateUppers k x c y
  updateDiseqs k x c y

private def updateOccs (k : Int) (x : Var) (c : EqCnstr) : GoalM Unit := do
  let ys := (← get').occurs[x]!
  modify' fun s => { s with occurs := s.occurs.set x {} }
  updateOccsAt k x c x
  for y in ys do
    updateOccsAt k x c y

@[export lean_grind_cutsat_assert_eq]
def EqCnstr.assertImpl (c : EqCnstr) : GoalM Unit := do
  if (← inconsistent) then return ()
  trace[grind.cutsat.assert] "{← c.pp}"
  let c ← c.norm.applySubsts
  if c.p.isUnsatEq then
    trace[grind.cutsat.assert.unsat] "{← c.pp}"
    setInconsistent (.eq c)
    return ()
  if c.isTrivial then
    trace[grind.cutsat.assert.trivial] "{← c.pp}"
    return ()
  let k := c.p.gcdCoeffs'
  if c.p.getConst % k > 0 then
    setInconsistent (.eq c)
    return ()
  let c := if k == 1 then
    c
  else
    { p := c.p.div k, h := .divCoeffs c }
  let some (k, x) := c.p.pickVarToElim? | c.throwUnexpected
  trace[grind.debug.cutsat.subst] ">> {← getVar x}, {← c.pp}"
  trace[grind.cutsat.assert.store] "{← c.pp}"
  modify' fun s => { s with
    elimEqs := s.elimEqs.set x (some c)
    elimStack := x :: s.elimStack
  }
  updateOccs k x c
  if (← inconsistent) then return ()
  -- assert a divisibility constraint IF `|k| != 1`
  if k.natAbs != 1 then
    let p := c.p.insert (-k) x
    let d := Int.ofNat k.natAbs
    { d, p, h := .ofEq x c : DvdCnstr }.assert

private def exprAsPoly (a : Expr) : GoalM Poly := do
  if let some k ← getIntValue? a then
    return .num k
  else if let some var := (← get').varMap.find? { expr := a } then
    return .add 1 var (.num 0)
  else
    throwError "internal `grind` error, expression is not relevant to cutsat{indentExpr a}"

private def processNewIntEq (a b : Expr) : GoalM Unit := do
  let p₁ ← exprAsPoly a
  let p₂ ← exprAsPoly b
  -- Remark: we don't need to use the comm ring normalizer here because `p` is always linear.
  let p := p₁.combine (p₂.mul (-1))
  { p, h := .core a b p₁ p₂ : EqCnstr }.assert

/-- Asserts a constraint coming from the core. -/
private def EqCnstr.assertCore (c : EqCnstr) : GoalM Unit := do
  if let some (re, rp, p) ← c.p.normCommRing? then
    let c := { p, h := .commRingNorm c re rp : EqCnstr}
    c.assert
  else
    c.assert

/--
Similar to `natToInt`, but checks first whether the term has already been internalized.
-/
private def natToIntExt (a : Expr) : GoalM (Expr × Expr) := do
  if let some p := (← get').natToIntMap.find? { expr := a } then
    return p
  natToInt a

private def processNewNatEq (a b : Expr) : GoalM Unit := do
  let gen := max (← getGeneration a) (← getGeneration b)
  let (a', h₁) ← natToIntExt a
  let (b', h₂) ← natToIntExt b
  let thm := mkApp6 (mkConst ``Nat.ToInt.of_eq) a b a' b' h₁ h₂
  let lhs ← toLinearExpr a' gen
  let rhs ← toLinearExpr b' gen
  let p := lhs.sub rhs |>.norm
  let c := { p, h := .coreToInt a b thm lhs rhs : EqCnstr }
  c.assertCore

private def processNewToIntEq (a b : Expr) : ToIntM Unit := do
  let gen := max (← getGeneration a) (← getGeneration b)
  let (a', h₁) ← toInt a
  let (b', h₂) ← toInt b
  let thm := mkApp6 (← getInfo).ofEq a b a' b' h₁ h₂
  let lhs ← toLinearExpr a' gen
  let rhs ← toLinearExpr b' gen
  let p := lhs.sub rhs |>.norm
  let c := { p, h := .coreToInt a b thm lhs rhs : EqCnstr }
  c.assertCore

@[export lean_process_cutsat_eq]
def processNewEqImpl (a b : Expr) : GoalM Unit := do
  unless (← getConfig).cutsat do return ()
  if (← isNatTerm a <&&> isNatTerm b) then
    processNewNatEq a b
  else if (← isIntTerm a <&&> isIntTerm b) then
    processNewIntEq a b
  else
    let some α ← getToIntTermType? a | return ()
    let some β ← getToIntTermType? b | return ()
    unless isSameExpr α β do return ()
    ToIntM.run α do processNewToIntEq a b

private def processNewIntDiseq (a b : Expr) : GoalM Unit := do
  -- Remark: we don't need to use comm ring to normalize these polynomials because they are
  -- always linear.
  let p₁ ← exprAsPoly a
  let c ← if let some 0 ← getIntValue? b then
    pure { p := p₁, h := .core0 a b : DiseqCnstr }
  else
    let p₂ ← exprAsPoly b
    let p := p₁.combine (p₂.mul (-1))
    pure {p, h := .core a b p₁ p₂ : DiseqCnstr }
  c.assert

/-- Asserts a constraint coming from the core. -/
private def DiseqCnstr.assertCore (c : DiseqCnstr) : GoalM Unit := do
  if let some (re, rp, p) ← c.p.normCommRing? then
    let c := { p, h := .commRingNorm c re rp : DiseqCnstr }
    c.assert
  else
    c.assert

private def processNewNatDiseq (a b : Expr) : GoalM Unit := do
  let gen := max (← getGeneration a) (← getGeneration b)
  let (a', h₁) ← natToIntExt a
  let (b', h₂) ← natToIntExt b
  let thm := mkApp6 (mkConst ``Nat.ToInt.of_diseq) a b a' b' h₁ h₂
  let lhs ← toLinearExpr a' gen
  let rhs ← toLinearExpr b' gen
  let p := lhs.sub rhs |>.norm
  let c := { p, h := .coreToInt a b thm lhs rhs : DiseqCnstr }
  c.assertCore
  return ()

private def processNewToIntDiseq (a b : Expr) : ToIntM Unit := do
  let gen := max (← getGeneration a) (← getGeneration b)
  let (a', h₁) ← toInt a
  let (b', h₂) ← toInt b
  let thm := mkApp6 (← getInfo).ofDiseq a b a' b' h₁ h₂
  let lhs ← toLinearExpr a' gen
  let rhs ← toLinearExpr b' gen
  let p := lhs.sub rhs |>.norm
  let c := { p, h := .coreToInt a b thm lhs rhs : DiseqCnstr }
  c.assertCore

@[export lean_process_cutsat_diseq]
def processNewDiseqImpl (a b : Expr) : GoalM Unit := do
  unless (← getConfig).cutsat do return ()
  if (← isNatTerm a <&&> isNatTerm b) then
    processNewNatDiseq a b
  else if (← isIntTerm a <&&> isIntTerm b) then
    processNewIntDiseq a b
  else
    let some α ← getToIntTermType? a | return ()
    let some β ← getToIntTermType? b | return ()
    unless isSameExpr α β do return ()
    ToIntM.run α do processNewToIntDiseq a b

/-- Different kinds of terms internalized by this module. -/
private inductive SupportedTermKind where
  | add | mul | num | div | mod | sub | pow | natAbs | toNat | natCast | neg | toInt | finVal
  deriving BEq, Repr

private def getKindAndType? (e : Expr) : Option (SupportedTermKind × Expr) :=
  match_expr e with
  | HAdd.hAdd α _ _ _ _ _ => some (.add, α)
  | HSub.hSub α _ _ _ _ _ => some (.sub, α)
  | HMul.hMul α _ _ _ _ _ => some (.mul, α)
  | HDiv.hDiv α _ _ _ _ _ => some (.div, α)
  | HMod.hMod α _ _ _ _ _ => some (.mod, α)
  | HPow.hPow α _ _ _ _ _ => some (.pow, α)
  | OfNat.ofNat α _ _     => some (.num, α)
  | Neg.neg α _ a =>
    let_expr OfNat.ofNat _ _ _ := a | some (.neg, α)
    some (.num, α)
  | Int.natAbs _ => some (.natAbs, Nat.mkType)
  | Int.toNat _ => some (.toNat, Nat.mkType)
  | NatCast.natCast α _ _ => some (.natCast, α)
  | Fin.val _ _ => some (.finVal, Nat.mkType)
  | Grind.ToInt.toInt _ _ _ _ => some (.toInt, Int.mkType)
  | _ => none

private def isForbiddenParent (parent? : Option Expr) (k : SupportedTermKind) : Bool := Id.run do
  let some parent := parent? | return false
  let .const declName _ := parent.getAppFn | return false
  -- TODO: document `NatCast.natCast` case.
  -- Remark: we added it to prevent natCast_sub from being expanded twice.
  if declName == ``NatCast.natCast then return true
  if k matches .div | .mod | .sub | .pow | .neg | .natAbs | .toNat | .natCast | .toInt | .finVal then return false
  if declName == ``HAdd.hAdd || declName == ``LE.le || declName == ``Dvd.dvd then return true
  match k with
  | .add => return false
  | .mul => return declName == ``HMul.hMul
  | .num =>
    -- Recall that we don't want to internalize numerals occurring at terms such as `x^3`.
    return declName == ``HMul.hMul || declName == ``HPow.hPow
  | _ => unreachable!

private def internalizeInt (e : Expr) : GoalM Unit := do
  if (← hasVar e) then return ()
  let p ← toPoly e
  trace[grind.debug.cutsat.internalize] "{aquote e}:= {← p.pp}"
  let x ← mkVar e
  if p == .add 1 x (.num 0) then
    -- It is pointless to assert `x = x`
    -- This can happen if `e` is a nonlinear term (e.g., `e` is `a*b`)
    return
  if let some (re, rp, p') ← p.normCommRing? then
    let c := { p := .add (-1) x p', h := .defnCommRing e p re rp p' : EqCnstr }
    c.assert
  else
    let c := { p := .add (-1) x p, h := .defn e p : EqCnstr }
    c.assert

private def expandDivMod (a : Expr) (b : Int) : GoalM Unit := do
  if b == 0 || b == 1 || b == -1 then
    throwError "`grind` internal error, found non-normalized div/mod by {b}"
  if (← get').divMod.contains (a, b) then return ()
  modify' fun s => { s with divMod := s.divMod.insert (a, b) }
  let n : Int := 1 - b.natAbs
  let b := mkIntLit b
  pushNewFact <| mkApp2 (mkConst ``Int.Linear.ediv_emod) a b
  pushNewFact <| mkApp3 (mkConst ``Int.Linear.emod_nonneg) a b reflBoolTrue
  pushNewFact <| mkApp4 (mkConst ``Int.Linear.emod_le) a b (toExpr n) reflBoolTrue

private def propagateDiv (e : Expr) : GoalM Unit := do
  let_expr HDiv.hDiv _ _ _ inst a b ← e | return ()
  if (← isInstHDivInt inst) then
    let some b ← getIntValue? b | return ()
    -- Remark: we currently do not consider the case where `b` is in the equivalence class of a numeral.
    expandDivMod a b

private def propagateMod (e : Expr) : GoalM Unit := do
  let_expr HMod.hMod _ _ _ inst a b ← e | return ()
  if (← isInstHModInt inst) then
    let some b ← getIntValue? b | return ()
    expandDivMod a b

private def propagateToInt (e : Expr) : GoalM Unit := do
  let_expr Grind.ToInt.toInt α _ _ a := e | return ()
  if (← isToIntTerm a) then return ()
  let some (eToInt, he) ← toInt? a α | return ()
  discard <| mkVar e
  if isSameExpr e eToInt then return ()
  modify' fun s => { s with
    toIntTermMap := s.toIntTermMap.insert { expr := a } { eToInt, he, α }
  }
  let prop := mkIntEq e eToInt
  pushNewFact <| mkExpectedPropHint he prop

private def propagateNatAbs (e : Expr) : GoalM Unit := do
  let_expr Int.natAbs a := e | return ()
  pushNewFact <| mkApp (mkConst ``Lean.Omega.Int.ofNat_natAbs) a

private def propagateToNat (e : Expr) : GoalM Unit := do
  let_expr Int.toNat a := e | return ()
  pushNewFact <| mkApp (mkConst ``Nat.ToInt.ofNat_toNat) a

private def isToIntForbiddenParent (parent? : Option Expr) : Bool :=
  if let some parent := parent? then
    getKindAndType? parent |>.isSome
  else
    false

private def internalizeIntTerm (e type : Expr) (parent? : Option Expr) (k : SupportedTermKind) : GoalM Unit := do
  if isForbiddenParent parent? k then return ()
  trace[grind.debug.cutsat.internalize] "{e} : {type}"
  match k with
  | .div => propagateDiv e
  | .mod => propagateMod e
  | .toInt => propagateToInt e
  | _ => internalizeInt e

private def internalizeNatTerm (e type : Expr) (parent? : Option Expr) (k : SupportedTermKind) : GoalM Unit := do
  if (← isNatTerm e) then return () -- already internalized
  match k with
  | .natAbs => propagateNatAbs e
  | .toNat => propagateToNat e
  | _ => pure ()
  if isForbiddenParent parent? k then return ()
  if (← get').natToIntMap.contains { expr := e } then return ()
  let e'h ← natToInt e
  trace[grind.debug.cutsat.internalize] "{e} : {type}"
  trace[grind.debug.cutsat.toInt] "{e} ==> {e'h.1}"
  modify' fun s => { s with
    natToIntMap := s.natToIntMap.insert { expr := e } e'h
  }
  markAsCutsatTerm e
  /-
  If `e'.h` is of the form `NatCast.natCast e`, then it is wasteful to
  assert an equality
  -/
  match_expr e'h.1 with
  | NatCast.natCast _ _ a => if e == a then return ()
  | _ => pure ()
  let e'' ← toLinearExpr e'h.1
  let p := e''.norm
  let natCast_e ← shareCommon (mkIntNatCast e)
  let gen ← getGeneration e
  internalize natCast_e gen
  let x ← mkVar natCast_e
  modify' fun s => { s with natDef := s.natDef.insert { expr := e } x }
  if let some (re, rp, p') ← p.normCommRing? then
    let c := { p := .add (-1) x p', h := .defnNatCommRing e'h.2 x e'' p re rp p' : EqCnstr }
    c.assert
  else
    let c := { p := .add (-1) x p, h := .defnNat e'h.2 x e'' : EqCnstr }
    c.assert

private def internalizeToIntTerm (e type : Expr) : GoalM Unit := do
  if (← isToIntTerm e) then return () -- already internalized
  if let some (eToInt, he) ← toInt? e type then
    trace[grind.debug.cutsat.internalize] "{e} : {type}"
    trace[grind.debug.cutsat.toInt] "{e} ==> {eToInt}"
    let α := type
    modify' fun s => { s with
      toIntTermMap := s.toIntTermMap.insert { expr := e } { eToInt, he, α }
    }
    markAsCutsatTerm e

/--
Internalizes an integer (and `Nat`) expression. Here are the different cases that are handled.

- `a + b` when `parent?` is not `+`, `≤`, or `∣`
- `k * a` when `k` is a numeral and `parent?` is not `+`, `*`, `≤`, `∣`
- numerals when `parent?` is not `+`, `*`, `≤`, `∣`.
  Recall that we must internalize numerals to make sure we can propagate equalities
  back to the congruence closure module. Example: we have `f 5`, `f x`, `x - y = 3`, `y = 2`.
-/
def internalize (e : Expr) (parent? : Option Expr) : GoalM Unit := do
  unless (← getConfig).cutsat do return ()
  if let some (k, type) := getKindAndType? e then
    if type.isConstOf ``Int then
      internalizeIntTerm e type parent? k
    else if type.isConstOf ``Nat then
      internalizeNatTerm e type parent? k
    else
      if isToIntForbiddenParent parent? then return ()
      internalizeToIntTerm e type
  else
    /-
    Remark: types implementing the `ToInt` class have a finite number
    of elements. Thus, we must internalize all of them. Otherwise,
    `grind` would fail to solve
    ```
    example (a : Fin 2) : a ≠ 0 → a ≠ 1 → False := by
      grind
    ```
    It is not sufficient to internalize only the terms occurring in equalities and inequalities.
    Here is an example where we must internalize `a`.
    ```
    example (a : Fin 2) (f : Fin 2 → Nat) : f 0 = 1 → f 1 = 1 → f a = 1 → False := by
      grind
    ```
    Note that is not sufficient to internalize only the local declarations (e.g., `a`).
    ```
    example (g : Nat → Fin 2) (f : Fin 2 → Nat) : f 0 = 1 → f 1 = 1 → f (g 1) = 1 → False := by
      grind
    ```
    That said, we currently do **not** support model-based theory combination for `ToInt` types.
    Thus, we consider the extra terms occurring in equalities.

    Recall that skip internalizing `Int` variables occurring in terms such as
    ```
    a = b
    ```
    is fine, because `Int` has an infinite number of elements, just using
    the information in core, we can always find an assignment for them if even they have
    not been internalized.

    TODO: infer type and internalize all terms `a : α` s.t. `[ToInt α]` after we add
    model-based theory combination for `ToInt`. One concern is performance, we will have
    to use `inferType` again, and perform some form of canonicalization. Running
    `ToInt` for them may be too expensive because the `ToInt` type class has output parameters.
    Perhaps, we should have a `HasToInt` auxiliary class without output parameters.
    -/
    let_expr Eq α a b := e | return ()
    unless (← getToIntId? α).isSome do return ()
    internalizeToIntTerm a α
    internalizeToIntTerm b α

end Lean.Meta.Grind.Arith.Cutsat
