import Lean.Meta

/-!
# Tests for the `inlineExpr` function

`inlineExpr` should print the given expression inline, unless it exceeds a given length, in which
case it is moved to an indented block.
-/

open Lean Meta

opaque shortFun : Nat → Nat
opaque shortConst : Nat

def runTest (e : Expr) : MetaM Unit := do
  let msg := inlineExpr e (maxInlineLength := 30)
  logInfo m!"Before{msg}After"

def testShort : MetaM Unit := do
  runTest <| .app (.const ``shortFun []) (.const ``shortConst [])

/-- info: Before shortFun shortConst After -/
#guard_msgs in
#eval testShort

opaque functionWithLongName : Nat → Nat
opaque constantWithLongName : Nat

def testLong : MetaM Unit := do
  runTest <| .app (.const ``functionWithLongName []) (.const ``constantWithLongName [])

/--
info: Before
  functionWithLongName constantWithLongName
After
-/
#guard_msgs in
#eval testLong
