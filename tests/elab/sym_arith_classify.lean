import Lean

/-!
# Tests for `Sym.Arith.Classify`, `Sym.Arith.EvalNum`, and `Sym.Arith.Functions`
-/

open Lean Meta Sym Arith

/-- Extract the value of a definition by name. -/
def getDefValue (n : Name) : MetaM Expr := do
  let some (.defnInfo info) := (← getEnv).find? n
    | throwError "expected definition: {n}"
  return info.value

/-! ## Classification tests -/

deriving instance Repr for ClassifyResult

/-- info: Lean.Meta.Sym.Arith.ClassifyResult.commRing 0 -/
#guard_msgs in
run_meta SymM.run do
  logInfo m!"{repr (← classify? (mkConst ``Int))}"

/-- info: Lean.Meta.Sym.Arith.ClassifyResult.commSemiring 0 -/
#guard_msgs in
run_meta SymM.run do
  logInfo m!"{repr (← classify? (mkConst ``Nat))}"

/-- info: Lean.Meta.Sym.Arith.ClassifyResult.none -/
#guard_msgs in
run_meta SymM.run do
  logInfo m!"{repr (← classify? (mkConst ``Bool))}"

-- Classifying the same type twice should return cached result with same id
/-- info: true -/
#guard_msgs in
run_meta SymM.run do
  let .commRing id1 ← classify? (mkConst ``Int) | unreachable!
  let .commRing id2 ← classify? (mkConst ``Int) | unreachable!
  logInfo m!"{id1 == id2}"

/--
info: Lean.Meta.Sym.Arith.ClassifyResult.commRing 0
---
info: Lean.Meta.Sym.Arith.ClassifyResult.commSemiring 0
---
info: Lean.Meta.Sym.Arith.ClassifyResult.commRing 2
---
info: Lean.Meta.Sym.Arith.ClassifyResult.commRing 1
-/
#guard_msgs in
run_meta SymM.run do
  let int ← shareCommon (mkConst ``Int)
  let nat ← shareCommon (mkConst ``Nat)
  let rat ← shareCommon (mkConst ``Rat)
  logInfo m!"{repr (← classify? int)}"
  logInfo m!"{repr (← classify? nat)}"
  logInfo m!"{repr (← classify? rat)}"
  let inst ← Sym.synthInstance (mkApp (mkConst ``Grind.Semiring [0]) nat)
  let ofSemiring ← shareCommon (← Sym.canon <| mkApp2 (mkConst ``Grind.Ring.OfSemiring.Q [0]) nat inst)
  logInfo m!"{repr (← classify? ofSemiring)}"

/-! ## EvalNum tests -/

def natZero : Nat := 0
def natSucc3 : Nat := Nat.succ (Nat.succ (Nat.succ 0))
def natSeven : Nat := 7
def natAdd : Nat := 2 + 3
def natMul : Nat := 2 * 3
def natPow : Nat := 2 ^ 3
def natBigPow : Nat := 2 ^ 100
def natPow10 : Nat := 2 ^ 10

/-- info: some (0) -/
#guard_msgs in
run_meta SymM.run do
  logInfo m!"{← evalNat? (← getDefValue ``natZero)}"

/-- info: some (3) -/
#guard_msgs in
run_meta SymM.run do
  logInfo m!"{← evalNat? (← getDefValue ``natSucc3)}"

/-- info: some (7) -/
#guard_msgs in
run_meta SymM.run do
  logInfo m!"{← evalNat? (← getDefValue ``natSeven)}"

/-- info: some (5) -/
#guard_msgs in
run_meta SymM.run do
  logInfo m!"{← evalNat? (← getDefValue ``natAdd)}"

/-- info: some (6) -/
#guard_msgs in
run_meta SymM.run do
  logInfo m!"{← evalNat? (← getDefValue ``natMul)}"

/-- info: some (8) -/
#guard_msgs in
run_meta SymM.run do
  logInfo m!"{← evalNat? (← getDefValue ``natPow)}"

/-! ## Exp threshold tests -/

-- The default threshold matches `Grind.Config.exp`, so `2 ^ 100` is evaluated eagerly
/-- info: some (1267650600228229401496703205376) -/
#guard_msgs in
run_meta SymM.run do
  logInfo m!"{← evalNat? (← getDefValue ``natBigPow)}"

-- 2 ^ 100 fails with the threshold lowered to 8
/-- info: none -/
#guard_msgs in
run_meta SymM.run do
  withExpThreshold 8 do
    logInfo m!"{← evalNat? (← getDefValue ``natBigPow)}"

-- 2 ^ 10 succeeds with the threshold lowered to 20
/-- info: some (1024) -/
#guard_msgs in
run_meta SymM.run do
  withExpThreshold 20 do
    logInfo m!"{← evalNat? (← getDefValue ``natPow10)}"

-- `IsCharP (BitVec w) (2 ^ w)` needs the exponent `w` evaluated under the default threshold
/-- info: char: some (18446744073709551616) -/
#guard_msgs in
run_meta SymM.run do
  let bv64 ← shareCommon (← Sym.canon (mkApp (mkConst ``BitVec) (mkNatLit 64)))
  let .commRing id ← classify? bv64 | throwError "expected commRing"
  logInfo m!"char: {(← getArithState).rings[id]!.charInst?.map (·.2)}"

/-! ## Int EvalNum tests -/

def intNeg : Int := -5
def intAdd : Int := 3 + (-2)
def intMul : Int := (-3) * 4

/-- info: some (-5) -/
#guard_msgs in
run_meta SymM.run do
  logInfo m!"{← evalInt? (← getDefValue ``intNeg)}"

/-- info: some (1) -/
#guard_msgs in
run_meta SymM.run do
  logInfo m!"{← evalInt? (← getDefValue ``intAdd)}"

/-- info: some (-12) -/
#guard_msgs in
run_meta SymM.run do
  logInfo m!"{← evalInt? (← getDefValue ``intMul)}"

/-! ## `Ring.OfSemiring.Q` fast path -/

-- Classifying the envelope directly must take the fast path: the `CommRing (Q Nat)` instance
-- is registered as an override instead of being synthesized, and the conditional
-- `IsCharP`/`NoNatZeroDivisors` instances are derived from the `AddRightCancel` premise.
/-- info: char: some (0), noZeroDiv: true, field: false, powIdentity: none, registered: true -/
#guard_msgs in
run_meta SymM.run do
  let nat ← shareCommon (mkConst ``Nat)
  let commSemiringInst ← Sym.synthInstance (mkApp (mkConst ``Grind.CommSemiring [0]) nat)
  let semiringInst := mkApp2 (mkConst ``Grind.CommSemiring.toSemiring [0]) nat commSemiringInst
  let q ← shareCommon (← Sym.canon <| mkApp2 (mkConst ``Grind.Ring.OfSemiring.Q [0]) nat semiringInst)
  let .commRing id ← classify? q | throwError "expected commRing"
  let ring := (← getArithState).rings[id]!
  let registered := (← get).instanceOverrides.contains (mkApp (mkConst ``Grind.CommRing [0]) q)
  logInfo m!"char: {ring.charInst?.map (·.2)}, noZeroDiv: {ring.noZeroDivInst?.isSome}, field: {ring.fieldInst?.isSome}, powIdentity: {ring.powIdentityInst?.map (·.2.2)}, registered: {registered}"

-- Classifying `Nat` creates the envelope through the same fast path and links it back.
/-- info: semiringId: some (0), registered: true -/
#guard_msgs in
run_meta SymM.run do
  let nat ← shareCommon (mkConst ``Nat)
  let .commSemiring sid ← classify? nat | throwError "expected commSemiring"
  let sr := (← getArithState).semirings[sid]!
  let ring := (← getArithState).rings[sr.ringId]!
  let registered := (← get).instanceOverrides.contains (mkApp (mkConst ``Grind.CommRing [0]) ring.type)
  logInfo m!"semiringId: {ring.semiringId?}, registered: {registered}"

/-! ## `PowIdentity` -/

/-- info: powIdentity: some (2) -/
#guard_msgs in
run_meta SymM.run do
  let fin2 ← shareCommon (← Sym.canon (mkApp (mkConst ``Fin) (mkNatLit 2)))
  let .commRing id ← classify? fin2 | throwError "expected commRing"
  logInfo m!"powIdentity: {(← getArithState).rings[id]!.powIdentityInst?.map (·.2.2)}"

/-- info: powIdentity: none -/
#guard_msgs in
run_meta SymM.run do
  let .commRing id ← classify? (mkConst ``Int) | throwError "expected commRing"
  logInfo m!"powIdentity: {(← getArithState).rings[id]!.powIdentityInst?.map (·.2.2)}"
