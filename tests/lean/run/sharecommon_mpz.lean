import Lean

open Lean Meta Tactic Grind

def runGrind (x : GrindM α) : MetaM α := do
  GrindM.run x `dummy (← mkParams {}) (pure ())

@[noinline] def mkA (x : Nat) := x + 1

def tst (a b : Nat) : GrindM Unit := do
  IO.println a
  IO.println b
  let a ← shareCommon (mkNatLit a)
  let b ← shareCommon (mkNatLit b)
  IO.println (isSameExpr a b)

/--
info: 1000000000000000000000000001
1000000000000000000000000001
true
-/
#guard_msgs (info) in
run_meta do
  let a := mkA 1000000000000000000000000000
  let b := 1000000000000000000000000001
  runGrind (tst a b)

/--
info: 1001
1001
true
-/
#guard_msgs (info) in
run_meta do
  let a := mkA 1000
  let b := 1001
  runGrind (tst a b)

def tst2 (a b : Nat) : IO Unit := do
  IO.println a
  IO.println b
  let (a, b) := ShareCommon.shareCommon' (mkNatLit a, mkNatLit b)
  IO.println (isSameExpr a b)

/--
info: 1000000000000000000000000001
1000000000000000000000000001
true
-/
#guard_msgs (info) in
run_meta do
  let a := mkA 1000000000000000000000000000
  let b := 1000000000000000000000000001
  tst2 a b
