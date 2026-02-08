/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingId
import Lean.Meta.Tactic.Grind.Diseq
import Lean.Meta.Tactic.Grind.Arith.Util
import Lean.Meta.Tactic.Grind.Arith.CommRing.Proof
import Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr
import Lean.Meta.Tactic.Grind.Arith.CommRing.Inv
import Lean.Meta.Tactic.Grind.Arith.CommRing.Reify
import Lean.Meta.Tactic.Grind.Arith.CommRing.SafePoly
public section
namespace Lean.Meta.Grind.Arith.CommRing
/-- Returns `some ringId` if `a` and `b` are elements of the same ring. -/
private def inSameRing? (a b : Expr) : GoalM (Option Nat) := do
  let some ringId ← getTermRingId? a | return none
  let some ringId' ← getTermRingId? b | return none
  unless ringId == ringId' do return none -- This can happen when we have heterogeneous equalities
  return ringId

/-- Returns `some semiringId` if `a` and `b` are elements of the same semiring. -/
private def inSameSemiring? (a b : Expr) : GoalM (Option Nat) := do
  let some semiringId ← getTermSemiringId? a | return none
  let some semiringId' ← getTermSemiringId? b | return none
  unless semiringId == semiringId' do return none -- This can happen when we have heterogeneous equalities
  return semiringId

/-- Returns `some ringId` if `a` and `b` are elements of the same (non-commutative) ring. -/
private def inSameNonCommRing? (a b : Expr) : GoalM (Option Nat) := do
  let some ringId ← getTermNonCommRingId? a | return none
  let some ringId' ← getTermNonCommRingId? b | return none
  unless ringId == ringId' do return none -- This can happen when we have heterogeneous equalities
  return ringId

/-- Returns `some semiringId` if `a` and `b` are elements of the same (non-commutative) semiring. -/
private def inSameNonCommSemiring? (a b : Expr) : GoalM (Option Nat) := do
  let some semiringId ← getTermNonCommSemiringId? a | return none
  let some semiringId' ← getTermNonCommSemiringId? b | return none
  unless semiringId == semiringId' do return none -- This can happen when we have heterogeneous equalities
  return semiringId

def mkEqCnstr (p : Poly) (h : EqCnstrProof) : RingM EqCnstr := do
  let id := (← getCommRing).nextId
  let sugar := p.degree
  modifyCommRing fun s => { s with nextId := s.nextId + 1 }
  return { sugar, p, h, id }

/--
Returns the ring expression denoting the given Lean expression.
Recall that we compute the ring expressions during internalization.
-/
private def toRingExpr? [Monad m] [MonadLiftT GrindM m] [MonadRing m] (e : Expr) : m (Option RingExpr) := do
  let ring ← getRing
  if let some re := ring.denote.find? { expr := e } then
    return some re
  else if let some x := ring.varMap.find? { expr := e } then
    return some (.var x)
  else
    reportIssue! "failed to convert to ring expression{indentExpr e}"
    return none

/--
Returns the semiring expression denoting the given Lean expression.
Recall that we compute the semiring expressions during internalization.
-/
private def toSemiringExpr? [Monad m] [MonadLiftT GrindM m] [MonadSemiring m] (e : Expr) : m (Option SemiringExpr) := do
  let semiring ← getSemiring
  if let some re := semiring.denote.find? { expr := e } then
    return some re
  else if let some x := semiring.varMap.find? { expr := e } then
    return some (.var x)
  else
    reportIssue! "failed to convert to semiring expression{indentExpr e}"
    return none

/--
Returns `some c`, where `c` is an equation from the basis whose leading monomial divides `m`.
Remark: if the current ring does not satisfy the property
```
∀ (k : Nat) (a : α), k ≠ 0 → OfNat.ofNat (α := α) k * a = 0 → a = 0
```
then the leading coefficient of the equation must also divide `k`
-/
def _root_.Lean.Grind.CommRing.Mon.findSimp? (k : Int) (m : Mon) : RingM (Option EqCnstr) := do
  let checkCoeff ← checkCoeffDvd
  let noZeroDiv ← noZeroDivisors
  for c in (← getCommRing).basis do
    if !checkCoeff || noZeroDiv || (c.p.lc ∣ k) then
    if c.p.divides m then
      return some c
  return none

/--
Returns `some c`, where `c` is an equation from the basis whose leading monomial divides some
monomial in `p`.
-/
def _root_.Lean.Grind.CommRing.Poly.findSimp? (p : Poly) : RingM (Option EqCnstr) := do
  match p with
  | .num _ => return none
  | .add k m p =>
    match (← m.findSimp? k) with
    | some c => return some c
    | none => p.findSimp?

/-- Simplifies `d.p` using `c`, and returns an extended polynomial derivation. -/
def PolyDerivation.simplifyWith (d : PolyDerivation) (c : EqCnstr) : RingM PolyDerivation := do
  let some r := d.p.simp? c.p (← nonzeroChar?) | return d
  incSteps
  trace_goal[grind.ring.simp] "{← r.p.denoteExpr}"
  return .step r.p r.k₁ d r.k₂ r.m₂ c

def PolyDerivation.simplifyNumEq0 (d : PolyDerivation) : RingM PolyDerivation := do
  let some numEq0 := (← getCommRing).numEq0? | return d
  let .num k := numEq0.p | return d
  return .normEq0 (d.p.normEq0 k.natAbs) d numEq0

/-- Simplified `d.p` using the current basis, and returns the extended polynomial derivation. -/
def PolyDerivation.simplify (d : PolyDerivation) : RingM PolyDerivation := do
  let mut d := d
  repeat
    d ← d.simplifyNumEq0
    if (← checkMaxSteps) then return d
    let some c ← d.p.findSimp? |
      trace_goal[grind.debug.ring.simp] "simplified{indentD (← d.denoteExpr)}"
      return d
    d ← d.simplifyWith c
  return d

/-- Simplifies `c₁` using `c₂`. -/
def EqCnstr.simplifyWithCore (c₁ c₂ : EqCnstr) : RingM (Option EqCnstr) := do
  let some r := c₁.p.simp? c₂.p (← nonzeroChar?) | return none
  let c := { c₁ with
    p := r.p
    h := .simp r.k₁ c₁ r.k₂ r.m₂ c₂
  }
  incSteps
  trace_goal[grind.ring.simp] "{← c.p.denoteExpr}"
  return some c

/-- Simplifies `c₁` using `c₂`. -/
def EqCnstr.simplifyWith (c₁ c₂ : EqCnstr) : RingM EqCnstr := do
  let some c ← c₁.simplifyWithCore c₂ | return c₁
  return c

/-- Simplifies `c₁` using `c₂` exhaustively. -/
partial def EqCnstr.simplifyWithExhaustively (c₁ c₂ : EqCnstr) : RingM EqCnstr := do
  let some c ← c₁.simplifyWithCore c₂ | return c₁
  c.simplifyWithExhaustively c₂

def EqCnstr.simplifyUsingNumEq0 (c : EqCnstr) : RingM EqCnstr := do
  let some c' := (← getCommRing).numEq0? | return c
  let .num k := c'.p | return c
  return { c with p := c.p.normEq0 k.natAbs, h := .numEq0 k.natAbs c' c }

/-- Simplify the given equation constraint using the current basis. -/
def EqCnstr.simplify (c : EqCnstr) : RingM EqCnstr := do
  let mut c := c
  repeat
    c ← simplifyUsingNumEq0 c
    if (← checkMaxSteps) then return c
    let some c' ← c.p.findSimp? |
      trace_goal[grind.debug.ring.simp] "simplified{indentD (← c.denoteExpr)}"
      return c
    c ← c.simplifyWith c'
  return c

/-- Returns `true` if `c.p` is the constant polynomial. -/
def EqCnstr.checkConstant (c : EqCnstr) : RingM Bool := do
  let .num n := c.p | return false
  if n == 0 then
    trace_goal[grind.ring.assert.trivial] "{← c.denoteExpr}"
  else if (← hasChar) then
    c.setUnsat
  else if (← pure (n.natAbs == 1) <&&> isField) then
    c.setUnsat
  else
    let mut c := c
    let mut n := n
    if n < 0 then
      n := -n
      c := { c with p := .num n, h := .mul (-1) c }
    if let some c' := (← getCommRing).numEq0? then
      let .num m := c'.p | unreachable!
      let (g, a, b) := gcdExt n m
      c := { c with p := .num g, h := .gcd a b c c' }
    modifyCommRing fun s => { s with numEq0? := some c, numEq0Updated := true }
    trace_goal[grind.ring.assert.store] "{← c.denoteExpr}"
  return true

/--
Simplifies and checks whether the resulting constraint is trivial (i.e., `0 = 0`),
or inconsistent (i.e., `k = 0` where `k % c != 0` for a comm-ring with characteristic `c`),
and returns `none`. Otherwise, returns the simplified constraint.
-/
def EqCnstr.simplifyAndCheck (c : EqCnstr) : RingM (Option EqCnstr) := do
  let c ← c.simplify
  if (← c.checkConstant) then
    return none
  else
    return some c

private def addSorted (c : EqCnstr) : List EqCnstr → List EqCnstr
  | [] => [c]
  | c' :: cs =>
    if c.p.lm.grevlex c'.p.lm == .gt then
      c :: c' :: cs
    else
      c' :: addSorted c cs

def addToBasisCore (c : EqCnstr) : RingM Unit := do
  trace[grind.debug.ring.basis] "{← c.denoteExpr}"
  modifyCommRing fun s => { s with
    basis := addSorted c s.basis
    recheck := true
  }

def EqCnstr.addToQueue (c : EqCnstr) : RingM Unit := do
  if (← checkMaxSteps) then return ()
  trace_goal[grind.ring.assert.queue] "{← c.denoteExpr}"
  modifyCommRing fun s => { s with queue := s.queue.insert c }

def EqCnstr.superposeWith (c : EqCnstr) : RingM Unit := do
  if (← checkMaxSteps) then return ()
  let .add _ m _ := c.p | return ()
  for c' in (← getCommRing).basis do
    let .add _ m' _ := c'.p | pure ()
    if m.sharesVar m' then
      let r ← c.p.spolM c'.p
      trace_goal[grind.ring.superpose] "{← c.denoteExpr}\nwith: {← c'.denoteExpr}\nresult: {← r.spol.denoteExpr} = 0"
      addToQueue (← mkEqCnstr r.spol <| .superpose r.k₁ r.m₁ c r.k₂ r.m₂ c')

/--
Tries to convert the leading monomial into a monic one.

It exploits the fact that given a polynomial with leading coefficient `k`,
if the ring has a nonzero characteristic `p` and `gcd k p = 1`, then
`k` has an inverse.

It also handles the easy case where `k` is `-1`.

Remark: if the ring implements the class `NoNatZeroDivisors`, then
the coefficients are divided by the gcd of all coefficients.
-/
def EqCnstr.toMonic (c : EqCnstr) : RingM EqCnstr := do
  let k := c.p.lc
  if k == 1 then return c
  if let some p ← nonzeroChar? then
    let (g, α, _β) := gcdExt k p
    if g == 1 then
      -- `α*k + β*p = 1`
      -- `α*k = 1 (mod p)`
      let α := if α < 0 then α % p else α
      return { c with p := c.p.mulConstC α p, h := .mul α c }
  if (← noZeroDivisors) then
    let g : Int := c.p.gcdCoeffs
    if g != 1 then
      let g := if k < 0 then -g else g
      return { c with p := c.p.divConst g, h := .div g c }
  if k < 0 then
    return { c with p := c.p.mulConst (-1), h := .mul (-1) c }
  return c

def EqCnstr.simplifyBasis (c : EqCnstr) : RingM Unit := do
  trace[grind.debug.ring.simpBasis] "using: {← c.denoteExpr}"
  let .add _ m _ := c.p | return ()
  let rec go (basis : List EqCnstr) (acc : List EqCnstr) : RingM (List EqCnstr) := do
    match basis with
    | [] => return acc.reverse
    | c' :: basis =>
      match c'.p with
      | .add _ m' _ =>
        if m.divides m' then
          let c'' ← c'.simplifyWithExhaustively c
          trace[grind.debug.ring.simpBasis] "simplified: {← c''.denoteExpr}"
          unless (← checkConstant c'') do
            addToQueue c''
          go basis acc
        else
          go basis (c' :: acc)
      | _ => go basis (c' :: acc)
  let basis ← go (← getCommRing).basis []
  modifyCommRing fun s => { s with basis }

def EqCnstr.addToBasisAfterSimp (c : EqCnstr) : RingM Unit := do
  let c ← c.toMonic
  c.simplifyBasis
  c.superposeWith
  trace_goal[grind.ring.assert.basis] "{← c.denoteExpr}"
  addToBasisCore c

private def checkNumEq0Updated : RingM Unit := do
  if (← getCommRing).numEq0Updated then
    -- `numEq0?` was updated, then we must move the basis back to the queue to be simplified.
    let basis := (← getCommRing).basis
    modifyCommRing fun s => { s with numEq0Updated := false, basis := {} }
    for c in basis do
      c.addToQueue

@[inline] def withCheckingNumEq0 (k : RingM Unit) : RingM Unit := do
  try
    k
  finally
    checkNumEq0Updated

def EqCnstr.addToBasis (c : EqCnstr) : RingM Unit := do
  withCheckingNumEq0 do
    let some c ← c.simplifyAndCheck | return ()
    c.addToBasisAfterSimp

def addNewEq (c : EqCnstr) : RingM Unit := do
  withCheckingNumEq0 do
    let some c ← c.simplifyAndCheck | return ()
    if c.p.degree == 1 then
      c.addToBasisAfterSimp
    else
      c.addToQueue

/-- Returns `true` if `c.d.p` is the constant polynomial. -/
def DiseqCnstr.checkConstant (c : DiseqCnstr) : RingM Bool := do
  let .num k := c.d.p | return false
  if k == 0 then
    c.setUnsat
  else if (← hasChar) then
    trace_goal[grind.ring.assert.trivial] "{← c.denoteExpr}"
  return true

def DiseqCnstr.simplify (c : DiseqCnstr) : RingM DiseqCnstr :=
  withCheckCoeffDvd do
    -- We must enable `checkCoeffDvd := true`. See comments at `PolyDerivation`.
    return { c with d := (← c.d.simplify) }

def saveDiseq (c : DiseqCnstr) : RingM Unit := do
  trace_goal[grind.ring.assert.store] "{← c.denoteExpr}"
  modifyCommRing fun s => { s with diseqs := s.diseqs.push c }

def addNewDiseq (c : DiseqCnstr) : RingM Unit := do
  let c ← c.simplify
  if (← c.checkConstant) then
    return ()
  trace[grind.ring.assert.store] "{← c.denoteExpr}"
  saveDiseq c

def processNewEq (a b : Expr) : GoalM Unit := do
  if isSameExpr a b then return () -- TODO: check why this is needed
  if let some ringId ← inSameRing? a b then RingM.run ringId do
    trace_goal[grind.ring.assert] "{← mkEq a b}"
    let some ra ← toRingExpr? a | return ()
    let some rb ← toRingExpr? b | return ()
    let some p ← (ra.sub rb).toPolyM? | return ()
    addNewEq (← mkEqCnstr p (.core a b ra rb))
  else if let some semiringId ← inSameSemiring? a b then SemiringM.run semiringId do
    trace_goal[grind.ring.assert] "{← mkEq a b}"
    let some sa ← toSemiringExpr? a | return ()
    let some sb ← toSemiringExpr? b | return ()
    let lhs ← sa.denoteAsRingExpr
    let rhs ← sb.denoteAsRingExpr
    RingM.run (← getCommSemiring).ringId do
      let some ra ← reify? lhs (skipVar := false) (gen := (← getGeneration a)) | return ()
      let some rb ← reify? rhs (skipVar := false) (gen := (← getGeneration b)) | return ()
      let some p ← (ra.sub rb).toPolyM? | return ()
      addNewEq (← mkEqCnstr p (.coreS a b sa sb ra rb))

private def pre (e : Expr) : GoalM Expr := do
  -- We must canonicalize because the instances generated by this module may not match
  -- the ones selected by the canonicalizer
  shareCommon (← canon e)

private def diseqToEq (a b : Expr) : RingM Unit := do
  -- Rabinowitsch transformation
  let gen := max (← getGeneration a) (← getGeneration b)
  let ring ← getCommRing
  let some fieldInst := ring.fieldInst? | unreachable!
  let e ← pre <| mkApp2 (← getSubFn) a b
  modifyCommRing fun s => { s with invSet := s.invSet.insert e }
  let eInv ← pre <| mkApp (← getInvFn) e
  let lhs ← pre <| mkApp2 (← getMulFn) e eInv
  internalize lhs gen none
  trace[grind.debug.ring.rabinowitsch] "{lhs}"
  pushEq lhs (← getOne) <| mkApp5 (mkConst ``Grind.CommRing.diseq_to_eq [ring.u]) ring.type fieldInst a b (← mkDiseqProof a b)

private def diseqZeroToEq (a b : Expr) : RingM Unit := do
  -- Rabinowitsch transformation for `b = 0` case
  let gen ← getGeneration a
  let ring ← getCommRing
  let some fieldInst := ring.fieldInst? | unreachable!
  modifyCommRing fun s => { s with invSet := s.invSet.insert a }
  let aInv ← pre <| mkApp (← getInvFn) a
  let lhs ← pre <| mkApp2 (← getMulFn) a aInv
  internalize lhs gen none
  trace[grind.debug.ring.rabinowitsch] "{lhs}"
  pushEq lhs (← getOne) <| mkApp4 (mkConst ``Grind.CommRing.diseq0_to_eq [ring.u]) ring.type fieldInst a (← mkDiseqProof a b)

private def processNewDiseqCommRing (a b : Expr) : RingM Unit := do
  trace_goal[grind.ring.assert] "{mkNot (← mkEq a b)}"
  let some ra ← toRingExpr? a | return ()
  let some rb ← toRingExpr? b | return ()
  let some p ← (ra.sub rb).toPolyM? | return ()
  if (← isField) then
    if !(p matches .num _) || !(← hasChar) then
      if rb matches .num 0 then
        diseqZeroToEq a b
      else
        diseqToEq a b
      return ()
  addNewDiseq {
    lhs := a, rhs := b
    rlhs := ra, rrhs := rb
    d := .input p
    ofSemiring? := none
  }

private def processNewDiseqCommSemiring (a b : Expr) : SemiringM Unit := do
  if (← getAddRightCancelInst?).isSome then
    trace_goal[grind.ring.assert] "{mkNot (← mkEq a b)}"
    let some sa ← toSemiringExpr? a | return ()
    let some sb ← toSemiringExpr? b | return ()
    let lhs ← sa.denoteAsRingExpr
    let rhs ← sb.denoteAsRingExpr
    RingM.run (← getCommSemiring).ringId do
      let some ra ← reify? lhs (skipVar := false) (gen := (← getGeneration a)) | return ()
      let some rb ← reify? rhs (skipVar := false) (gen := (← getGeneration b)) | return ()
      let some p ← (ra.sub rb).toPolyM? | return ()
      addNewDiseq {
        lhs := a, rhs := b
        rlhs := ra, rrhs := rb
        d := .input p
        ofSemiring? := some (sa, sb)
      }
  else
    -- If semiring does not have `AddRightCancel`,
    -- we may still normalize and check whether lhs and rhs are equal
    let some sa ← toSemiringExpr? a | return ()
    let some sb ← toSemiringExpr? b | return ()
    if sa.toPoly == sb.toPoly then
      setSemiringDiseqUnsat a b sa sb

private def processNewDiseqNonCommRing (a b : Expr) : NonCommRingM Unit := do
  let some ra ← toRingExpr? a | return ()
  let some rb ← toRingExpr? b | return ()
  if let some (_, c) := (← getRing).charInst? then
    if ra.toPolyC_nc c == rb.toPolyC_nc c then
      setNonCommRingDiseqUnsat a b ra rb
  else
    if ra.toPoly_nc == rb.toPoly_nc then
      setNonCommRingDiseqUnsat a b ra rb

private def processNewDiseqNonCommSemiring (a b : Expr) : NonCommSemiringM Unit := do
  let some sa ← toSemiringExpr? a | return ()
  let some sb ← toSemiringExpr? b | return ()
  if sa.toPolyS_nc == sb.toPolyS_nc then
    setNonCommSemiringDiseqUnsat a b sa sb

def processNewDiseq (a b : Expr) : GoalM Unit := do
  if let some ringId ← inSameRing? a b then RingM.run ringId do
    processNewDiseqCommRing a b
  else if let some semiringId ← inSameSemiring? a b then SemiringM.run semiringId do
    processNewDiseqCommSemiring a b
  else if let some ncRingId ← inSameNonCommRing? a b then NonCommRingM.run ncRingId do
    processNewDiseqNonCommRing a b
  else if let some ncSemiringId ← inSameNonCommSemiring? a b then NonCommSemiringM.run ncSemiringId do
    processNewDiseqNonCommSemiring a b

/--
Returns `true` if the todo queue is not empty or the `recheck` flag is set to `true`
-/
private def needCheck : RingM Bool := do
  unless (← isQueueEmpty) do return true
  return (← getCommRing).recheck

private def checkDiseqs : RingM Unit := do
  let diseqs := (← getCommRing).diseqs
  modifyCommRing fun s => { s with diseqs := {} }
  -- No indexing simple
  for diseq in diseqs do
    addNewDiseq diseq
    if (← isInconsistent) then return

abbrev PropagateEqMap := Std.HashMap (Int × Poly) (Expr × RingExpr)

/--
Propagates implied equalities.
-/
private def propagateEqs : RingM Bool := do
  if (← isInconsistent) then return false
  /-
  This is a very simple procedure that does not use any indexing data-structure.
  We don't even cache the simplified polynomials.
  TODO: optimize
  TODO: support for semiring
  -/
  let go : StateT (Bool × PropagateEqMap) RingM Unit := do
    for a in (← getRing).vars do
      if (← checkMaxSteps) then return ()
      let some ra ← toRingExpr? a | unreachable!
      process a ra
    for (a, ra) in (← getCommRing).denoteEntries do
      if (← checkMaxSteps) then return ()
      process a ra
  let (_, (propagated, _)) ← go.run (false, {})
  return propagated
where
  process (a : Expr) (ra : RingExpr) : StateT (Bool × PropagateEqMap) RingM Unit := do
    let some p ← ra.toPolyM? | return ()
    let d : PolyDerivation := .input p
    let d ← d.simplify
    let k := d.getMultiplier
    trace_goal[grind.debug.ring.impEq] "{a}, {k}, {← d.p.denoteExpr}"
    if let some (b, rb) :=  (← get).2[(k, d.p)]? then
      -- TODO: use `isEqv` more effectively
      unless (← isEqv a b) do
        let some p ← (ra.sub rb).toPolyM? | return ()
        let d : PolyDerivation := .input p
        let d ← d.simplify
        if d.getMultiplier != 1 then
          unless (← noZeroDivisors) do
            -- Given the multiplier `k' = d.getMultiplier`, we have that `k*(a - b) = 0`,
            -- but we cannot eliminate the `k` because we don't have `noZeroDivisors`.
            trace_goal[grind.ring.impEq] "skip: {← mkEq a b}, k: {k}, noZeroDivisors: false"
            modify fun (propagated, map) => (propagated, map.insert (k, d.p) (a, ra))
            return ()
        trace_goal[grind.ring.impEq] "{← mkEq a b}, {k}, {← d.p.denoteExpr}"
        /-
        **Note**: If max number of steps has been reached, then `d.p` is not fully simplified.
        Recall that `propagateEq` assumes that it is.
        -/
        if (← checkMaxSteps) then return ()
        propagateEq a b ra rb d
        modify fun s => (true, s.2)
    else
      modify fun (propagated, map) => (propagated, map.insert (k, d.p) (a, ra))

def checkRing : RingM CheckResult := do
  unless (← needCheck) do return .none
  trace_goal[grind.debug.ring.check] "{(← getRing).type}"
  repeat
    checkSystem "ring"
    let some c ← getNext? | break
    trace_goal[grind.debug.ring.check] "{← c.denoteExpr}"
    c.addToBasis
    if (← isInconsistent) then return .closed
    if (← checkMaxSteps) then return .progress
  checkDiseqs
  if (← propagateEqs) then return .propagated
  modifyCommRing fun s => { s with recheck := false }
  return .progress

def check : GoalM CheckResult := do profileitM Exception "grind ring" (← getOptions) do
  if (← checkMaxSteps) then return .none
  let mut result : CheckResult := .none
  checkInvariants
  try
    for ringId in *...(← get').rings.size do
      let r ← RingM.run ringId checkRing
      result := result.join r
      if (← isInconsistent) then
        return .closed
    return result
  finally
    checkInvariants

def check' : GoalM Bool :=
  return (← check) != .none

end Lean.Meta.Grind.Arith.CommRing
