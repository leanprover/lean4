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

-- 2 ^ 100 should fail with default exp threshold (8)
/-- info: none -/
#guard_msgs in
run_meta SymM.run do
  logInfo m!"{← evalNat? (← getDefValue ``natBigPow)}"

-- 2 ^ 10 succeeds with exp threshold raised to 20
/-- info: some (1024) -/
#guard_msgs in
run_meta SymM.run do
  withExpThreshold 20 do
    logInfo m!"{← evalNat? (← getDefValue ``natPow10)}"

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
