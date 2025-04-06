/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Simp
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Var
import Lean.Meta.Tactic.Grind.Arith.Cutsat.DvdCnstr
import Lean.Meta.Tactic.Grind.Arith.Cutsat.LeCnstr

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
  trace[grind.cutsat.subst] "{← getVar x}, {← c₁.pp}, {← c₂.pp}"
  return { p, h := .subst x c₁ c₂ }

partial def DiseqCnstr.applySubsts (c : DiseqCnstr) : GoalM DiseqCnstr := withIncRecDepth do
  let some (x, c₁, p) ← c.p.substVar | return c
  trace[grind.cutsat.subst] "{← getVar x}, {← c.pp}, {← c₁.pp}"
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
    setInconsistent (.diseq c)
    return ()
  if c.isTrivial then
    trace[grind.cutsat.diseq.trivial] "{← c.pp}"
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
  trace[grind.cutsat.diseq] "{← c.pp}"
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
  trace[grind.cutsat.subst] "{← getVar x}, {← c.pp}, {← c₁.pp}"
  applySubsts { p, h := .subst x c₁ c : EqCnstr }

private def updateDvdCnstr (a : Int) (x : Var) (c : EqCnstr) (y : Var) : GoalM Unit := do
  let some c' := (← get').dvds[y]! | return ()
  let b := c'.p.coeff x
  if b == 0 then return ()
  modify' fun s => { s with dvds := s.dvds.set y none }
  let c' ← c'.applyEq a x c b
  c'.assert

private def split (x : Var) (cs : PArray LeCnstr) : GoalM (PArray LeCnstr × Array (Int × LeCnstr)) := do
  let mut cs' := {}
  let mut todo := #[]
  for c in cs do
    let b := c.p.coeff x
    if b == 0 then
      cs' := cs'.push c
    else
      todo := todo.push (b, c)
  return (cs', todo)

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
  let (lowers', todo) ← split x (← get').lowers[y]!
  modify' fun s => { s with lowers := s.lowers.set y lowers' }
  updateLeCnstrs a x c todo

/--
Given an equation `c₁` containing `a*x`, eliminate `x` from upper bound inequalities of `y`.
-/
private def updateUppers (a : Int) (x : Var) (c : EqCnstr) (y : Var) : GoalM Unit := do
  if (← inconsistent) then return ()
  let (uppers', todo) ← split x (← get').uppers[y]!
  modify' fun s => { s with uppers := s.uppers.set y uppers' }
  updateLeCnstrs a x c todo

private def splitDiseqs (x : Var) (cs : PArray DiseqCnstr) : GoalM (PArray DiseqCnstr × Array (Int × DiseqCnstr)) := do
  let mut cs' := {}
  let mut todo := #[]
  for c in cs do
    let b := c.p.coeff x
    if b == 0 then
      cs' := cs'.push c
    else
      todo := todo.push (b, c)
  return (cs', todo)

private def updateDiseqs (a : Int) (x : Var) (c : EqCnstr) (y : Var) : GoalM Unit := do
  if (← inconsistent) then return ()
  let (diseqs', todo) ← splitDiseqs x (← get').diseqs[y]!
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
    setInconsistent (.eq c)
    return ()
  if c.isTrivial then
    trace[grind.cutsat.eq.trivial] "{← c.pp}"
    return ()
  let k := c.p.gcdCoeffs'
  if c.p.getConst % k > 0 then
    setInconsistent (.eq c)
    return ()
  let c := if k == 1 then
    c
  else
    { p := c.p.div k, h := .divCoeffs c }
  trace[grind.cutsat.eq] "{← c.pp}"
  let some (k, x) := c.p.pickVarToElim? | c.throwUnexpected
  trace[grind.debug.cutsat.subst] ">> {← getVar x}, {← c.pp}"
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
  if let some var := (← get').varMap.find? { expr := a } then
    return .add 1 var (.num 0)
  else if let some k ← getIntValue? a then
    return .num k
  else
    throwError "internal `grind` error, expression is not relevant to cutsat{indentExpr a}"

private def processNewIntEq (a b : Expr) : GoalM Unit := do
  let p₁ ← exprAsPoly a
  let p₂ ← exprAsPoly b
  let p := p₁.combine (p₂.mul (-1))
  { p, h := .core a b p₁ p₂ : EqCnstr }.assert

private def processNewNatEq (a b : Expr) : GoalM Unit := do
  let (lhs, rhs) ← Int.OfNat.toIntEq a b
  let gen ← getGeneration a
  let ctx ← getForeignVars .nat
  let lhs' ← toLinearExpr (← lhs.denoteAsIntExpr ctx) gen
  let rhs' ← toLinearExpr (← rhs.denoteAsIntExpr ctx) gen
  let p := lhs'.sub rhs' |>.norm
  let c := { p, h := .coreNat a b lhs rhs lhs' rhs' : EqCnstr }
  trace[grind.debug.cutsat.nat] "{← c.pp}"
  c.assert

@[export lean_process_cutsat_eq]
def processNewEqImpl (a b : Expr) : GoalM Unit := do
  trace[grind.debug.cutsat.eq] "{a} = {b}"
  match (← foreignTerm? a), (← foreignTerm? b) with
  | none, none => processNewIntEq a b
  | some .nat, some .nat => processNewNatEq a b
  | _, _ => return ()

private def processNewIntLitEq (a ke : Expr) : GoalM Unit := do
  let some k ← getIntValue? ke | return ()
  let p₁ ← exprAsPoly a
  let c ← if k == 0 then
    pure { p := p₁, h := .core0 a ke : EqCnstr }
  else
    let p₂ ← exprAsPoly ke
    let p := p₁.combine (p₂.mul (-1))
    pure { p, h := .core a ke p₁ p₂ : EqCnstr }
  c.assert

@[export lean_process_cutsat_eq_lit]
def processNewEqLitImpl (a ke : Expr) : GoalM Unit := do
  trace[grind.debug.cutsat.eq] "{a} = {ke}"
  match (← foreignTerm? a) with
  | none => processNewIntLitEq a ke
  | some .nat => processNewNatEq a ke

private def processNewIntDiseq (a b : Expr) : GoalM Unit := do
  let p₁ ← exprAsPoly a
  let c ← if let some 0 ← getIntValue? b then
    pure { p := p₁, h := .core0 a b : DiseqCnstr }
  else
    let p₂ ← exprAsPoly b
    let p := p₁.combine (p₂.mul (-1))
    pure {p, h := .core a b p₁ p₂ : DiseqCnstr }
  c.assert

private def processNewNatDiseq (a b : Expr) : GoalM Unit := do
  let (lhs, rhs) ← Int.OfNat.toIntEq a b
  let gen ← getGeneration a
  let ctx ← getForeignVars .nat
  let lhs' ← toLinearExpr (← lhs.denoteAsIntExpr ctx) gen
  let rhs' ← toLinearExpr (← rhs.denoteAsIntExpr ctx) gen
  let p := lhs'.sub rhs' |>.norm
  let c := { p, h := .coreNat a b lhs rhs lhs' rhs' : DiseqCnstr }
  trace[grind.debug.cutsat.nat] "{← c.pp}"
  c.assert

@[export lean_process_cutsat_diseq]
def processNewDiseqImpl (a b : Expr) : GoalM Unit := do
  trace[grind.debug.cutsat.diseq] "{a} ≠ {b}"
  match (← foreignTerm? a), (← foreignTermOrLit? b) with
  | none, none => processNewIntDiseq a b
  | some .nat, some .nat => processNewNatDiseq a b
  | _, _ => return ()

/-- Different kinds of terms internalized by this module. -/
private inductive SupportedTermKind where
  | add | mul | num | div | mod | sub | natAbs | toNat
  deriving BEq

private def getKindAndType? (e : Expr) : Option (SupportedTermKind × Expr) :=
  match_expr e with
  | HAdd.hAdd α _ _ _ _ _ => some (.add, α)
  | HSub.hSub α _ _ _ _ _ => some (.sub, α)
  | HMul.hMul α _ _ _ _ _ => some (.mul, α)
  | HDiv.hDiv α _ _ _ _ _ => some (.div, α)
  | HMod.hMod α _ _ _ _ _ => some (.mod, α)
  | OfNat.ofNat α _ _ => some (.num, α)
  | Neg.neg α _ a =>
    let_expr OfNat.ofNat _ _ _ := a | none
    some (.num, α)
  | Int.natAbs _ => some (.natAbs, Nat.mkType)
  | Int.toNat _ => some (.toNat, Nat.mkType)
  | _ => none

private def isForbiddenParent (parent? : Option Expr) (k : SupportedTermKind) : Bool := Id.run do
  let some parent := parent? | return false
  let .const declName _ := parent.getAppFn | return false
  -- TODO: document `NatCast.natCast` case.
  -- Remark: we added it to prevent natCast_sub from being expanded twice.
  if declName == ``NatCast.natCast then return true
  if k matches .div | .mod | .sub | .natAbs | .toNat then return false
  if declName == ``HAdd.hAdd || declName == ``LE.le || declName == ``Dvd.dvd then return true
  match k with
  | .add => return false
  | .mul => return declName == ``HMul.hMul
  | .num => return declName == ``HMul.hMul || declName == ``Eq
  | _ => unreachable!

private def internalizeInt (e : Expr) : GoalM Unit := do
  if (← hasVar e) then return ()
  let p ← toPoly e
  trace[grind.cutsat.internalize] "{aquote e}:= {← p.pp}"
  let x ← mkVar e
  if p == .add 1 x (.num 0) then
    -- It is pointless to assert `x = x`
    -- This can happen if `e` is a nonlinear term (e.g., `e` is `a*b`)
    return
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

private def propagateNatSub (e : Expr) : GoalM Unit := do
  let_expr HSub.hSub _ _ _ inst a b := e | return ()
  unless (← isInstHSubNat inst) do return ()
  discard <| mkForeignVar a .nat
  discard <| mkForeignVar b .nat
  pushNewFact <| mkApp2 (mkConst ``Int.Linear.natCast_sub) a b

private def propagateNatAbs (e : Expr) : GoalM Unit := do
  let_expr Int.natAbs a := e | return ()
  pushNewFact <| mkApp (mkConst ``Lean.Omega.Int.ofNat_natAbs) a

private def propagateToNat (e : Expr) : GoalM Unit := do
  let_expr Int.toNat a := e | return ()
  pushNewFact <| mkApp (mkConst ``Int.OfNat.ofNat_toNat) a

/--
Internalizes an integer (and `Nat`) expression. Here are the different cases that are handled.

- `a + b` when `parent?` is not `+`, `≤`, or `∣`
- `k * a` when `k` is a numeral and `parent?` is not `+`, `*`, `≤`, `∣`
- numerals when `parent?` is not `+`, `*`, `≤`, `∣`, `=`.
  Recall that we must internalize numerals to make sure we can propagate equalities
  back to the congruence closure module. Example: we have `f 5`, `f x`, `x - y = 3`, `y = 2`.
-/
def internalize (e : Expr) (parent? : Option Expr) : GoalM Unit := do
  let some (k, type) := getKindAndType? e | return ()
  if isForbiddenParent parent? k then return ()
  trace[grind.debug.cutsat.internalize] "{e} : {type}"
  if type.isConstOf ``Int then
    match k with
    | .div => propagateDiv e
    | .mod => propagateMod e
    | .num => pure ()
    | _ => internalizeInt e
  else if type.isConstOf ``Nat then
    discard <| mkForeignVar e .nat
    match k with
    | .sub => propagateNatSub e
    | .natAbs => propagateNatAbs e
    | .toNat => propagateToNat e
    | _ => pure ()

end Lean.Meta.Grind.Arith.Cutsat
