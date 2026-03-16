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

/-- info: Before `shortFun shortConst` After -/
#guard_msgs in
#eval runTest <| .app (.const ``shortFun []) (.const ``shortConst [])

opaque functionWithLongName : Nat → Nat
opaque constantWithLongName : Nat

/--
info: Before
  functionWithLongName constantWithLongName
After
-/
#guard_msgs in
#eval runTest <| .app (.const ``functionWithLongName []) (.const ``constantWithLongName [])

/-! Ensure that length computation accounts for namespace occlusion: -/

namespace ExceptionallyLongNamespaceThatWillNotBePrinted
opaque Bar.Baz : Nat → Nat

/--
info: Before `Bar.Baz Nat.zero` After
-/
#guard_msgs in
#eval runTest <| .app (.const ``Bar.Baz []) (.const ``Nat.zero [])

end ExceptionallyLongNamespaceThatWillNotBePrinted

/-! Test `trailing` variant: -/

def runTestTrailing (e : Expr) : MetaM Unit := do
  let msg := inlineExprTrailing e (maxInlineLength := 30)
  logInfo m!"Before{msg}"


/-- info: Before `shortFun shortConst` -/
#guard_msgs in
#eval runTestTrailing <| .app (.const ``shortFun []) (.const ``shortConst [])

/--
info: Before
  functionWithLongName constantWithLongName
-/
#guard_msgs in
#eval runTestTrailing <| .app (.const ``functionWithLongName []) (.const ``constantWithLongName [])
