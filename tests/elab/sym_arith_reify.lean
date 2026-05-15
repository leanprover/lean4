import Lean

/-!
# Tests for `Sym.Arith.Reify`
-/

open Lean Meta Sym Arith

/-- Extract the value of a definition by name. -/
def getDefValue (n : Name) : MetaM Expr := do
  let some (.defnInfo info) := (← getEnv).find? n
    | throwError "expected definition: {n}"
  return info.value

/-!
## Setup: a simple monad for testing reification
-/

structure TestState where
  ring : CommRing
  vars : Array Expr := {}
  varMap : PHashMap ExprPtr Var := {}

abbrev TestM := StateRefT TestState SymM

instance : MonadCanon TestM where
  canonExpr e := Sym.canon e
  synthInstance? e := Sym.synthInstance? e

instance : MonadCommRing TestM where
  getCommRing := return (← get).ring
  modifyCommRing f := modify fun s => { s with ring := f s.ring }

instance : MonadMkVar TestM where
  mkVar e := do
    if let some v := (← get).varMap.find? { expr := e } then
      return v
    let v := (← get).vars.size
    modify fun s => { s with
      vars := s.vars.push e
      varMap := s.varMap.insert { expr := e } v
    }
    return v

instance : MonadGetVar TestM where
  getVar x := return (← get).vars[x]!

/-- Run a `TestM` on `Int`'s `CommRing`, canonicalizing `e` first. -/
def reifyIntExpr (n : Name) (skipVar := true) : TestM (Option RingExpr) := do
  let e ← canonExpr (← getDefValue n)
  reifyRing? e (skipVar := skipVar)

def runTestOnInt (x : TestM α) : SymM α := do
  let .commRing id ← classify? (mkConst ``Int) | throwError "Int is not a CommRing"
  let ring := (← getArithState).rings[id]!
  x |>.run' { ring }

/-! ## Reify ring tests on Int -/

deriving instance Repr for Lean.Grind.CommRing.Expr

def intAdd : Int := 2 + 3
def intMulAdd : Int := 2 * 3 + 1
def intNeg : Int := -5
def intPow : Int := 2 ^ 3
def intSub : Int := 7 - 2

/-- info: some (Lean.Grind.CommRing.Expr.add (Lean.Grind.CommRing.Expr.num 2) (Lean.Grind.CommRing.Expr.num 3)) -/
#guard_msgs in
run_meta SymM.run do runTestOnInt do
  logInfo m!"{repr (← reifyIntExpr ``intAdd)}"

/--
info: some (Lean.Grind.CommRing.Expr.add
  (Lean.Grind.CommRing.Expr.mul (Lean.Grind.CommRing.Expr.num 2) (Lean.Grind.CommRing.Expr.num 3))
  (Lean.Grind.CommRing.Expr.num 1))
-/
#guard_msgs in
run_meta SymM.run do runTestOnInt do
  logInfo m!"{repr (← reifyIntExpr ``intMulAdd)}"

/-- info: some (Lean.Grind.CommRing.Expr.neg (Lean.Grind.CommRing.Expr.num 5)) -/
#guard_msgs in
run_meta SymM.run do runTestOnInt do
  logInfo m!"{repr (← reifyIntExpr ``intNeg)}"

/-- info: some (Lean.Grind.CommRing.Expr.pow (Lean.Grind.CommRing.Expr.num 2) 3) -/
#guard_msgs in
run_meta SymM.run do runTestOnInt do
  logInfo m!"{repr (← reifyIntExpr ``intPow)}"

/--
info: some (Lean.Grind.CommRing.Expr.sub (Lean.Grind.CommRing.Expr.num 7) (Lean.Grind.CommRing.Expr.num 2))
-/
#guard_msgs in
run_meta SymM.run do runTestOnInt do
  logInfo m!"{repr (← reifyIntExpr ``intSub)}"

-- skipVar test: a non-arithmetic term returns none with skipVar=true
/-- info: none -/
#guard_msgs in
run_meta SymM.run do runTestOnInt do
  let a ← mkFreshExprMVar (mkConst ``Int)
  logInfo m!"{repr (← reifyRing? a)}"

-- skipVar=false: a non-arithmetic term becomes a variable
/-- info: some (Lean.Grind.CommRing.Expr.var 0) -/
#guard_msgs in
run_meta SymM.run do runTestOnInt do
  let a ← mkFreshExprMVar (mkConst ``Int)
  logInfo m!"{repr (← reifyRing? a (skipVar := false))}"

opaque a : Int
opaque b : Int
opaque c : Int
def e := (a + b*2) - (c*a + a*(3*b + c))

/--
info: some (Lean.Grind.CommRing.Expr.sub
  (Lean.Grind.CommRing.Expr.add
    (Lean.Grind.CommRing.Expr.var 0)
    (Lean.Grind.CommRing.Expr.mul (Lean.Grind.CommRing.Expr.var 1) (Lean.Grind.CommRing.Expr.num 2)))
  (Lean.Grind.CommRing.Expr.add
    (Lean.Grind.CommRing.Expr.mul (Lean.Grind.CommRing.Expr.var 2) (Lean.Grind.CommRing.Expr.var 0))
    (Lean.Grind.CommRing.Expr.mul
      (Lean.Grind.CommRing.Expr.var 0)
      (Lean.Grind.CommRing.Expr.add
        (Lean.Grind.CommRing.Expr.mul (Lean.Grind.CommRing.Expr.num 3) (Lean.Grind.CommRing.Expr.var 1))
        (Lean.Grind.CommRing.Expr.var 2)))))
---
info: #[a, b, c]
-/
#guard_msgs in
run_meta SymM.run do runTestOnInt do
  logInfo m!"{repr (← reifyIntExpr ``e)}"
  logInfo (← get).vars

/-! ## Roundtrip tests: reify then denote -/

/-- Reify an expression, denote it back, and check they're definitionally equal. -/
def roundtrip (n : Name) : TestM Unit := do
  let orig ← canonExpr (← getDefValue n)
  let some re ← reifyRing? orig (skipVar := false) | throwError "reify failed"
  let vars := (← get).vars
  let denoted ← denoteRingExpr vars re
  let denoted ← canonExpr denoted
  unless (← isDefEq orig denoted) do
    logInfo m!"MISMATCH for {n}:\n  orig:    {orig}\n  denoted: {denoted}"
    return
  logInfo m!"roundtrip OK: {n}: {denoted}"

/--
info: roundtrip OK: intAdd: 2 + 3
---
info: roundtrip OK: intMulAdd: 2 * 3 + 1
---
info: roundtrip OK: intNeg: -5
---
info: roundtrip OK: intPow: 2 ^ 3
---
info: roundtrip OK: intSub: 7 - 2
---
info: roundtrip OK: e: a + b * 2 - (c * a + a * (3 * b + c))
-/
#guard_msgs in
run_meta SymM.run do runTestOnInt do
  roundtrip ``intAdd
  roundtrip ``intMulAdd
  roundtrip ``intNeg
  roundtrip ``intPow
  roundtrip ``intSub
  roundtrip ``e
