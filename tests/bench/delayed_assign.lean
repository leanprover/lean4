import Lean

open Lean Meta

def mkLE (i : Nat) : Expr :=
  mkNatLE (mkNatLit 0) (mkBVar i)

partial def solve (mvarId : MVarId) : MetaM Unit := do
  let type ← instantiateMVars (← mvarId.getType)
  if type.isForall then
    let (_, mvarId) ← mvarId.intro1
    solve mvarId
  else if type.isAppOf ``And then
    let [mvarId₁, mvarId₂] ← mvarId.applyConst ``And.intro | failure
    solve mvarId₁
    solve mvarId₂
  else if type.isAppOf ``LE.le then
    let [] ← mvarId.applyConst ``Nat.zero_le | failure
  else
    let [] ← mvarId.applyConst ``True.intro | failure

partial def runBench (name : String) (n : Nat) (mk : Nat → MetaM MVarId) : MetaM Unit := do
  let mvarId ← mk n
  let startTime ← IO.monoNanosNow
  solve mvarId
  let endTime ← IO.monoNanosNow
  let ms := (endTime - startTime).toFloat / 1000000.0
  let startTime ← IO.monoNanosNow
  discard <| instantiateMVars (mkMVar mvarId)
  let endTime ← IO.monoNanosNow
  let instMs := (endTime - startTime).toFloat / 1000000.0
  IO.println s!"{name}_{n}: {ms} ms, instantiateMVars: {instMs} ms"

def mkBench1 (n : Nat) : MetaM MVarId := do
  let type := mkType n
  return (← mkFreshExprSyntheticOpaqueMVar type).mvarId!
where
  mkResultType (i : Nat) : Expr :=
    match i with
    | 0 => mkConst ``True
    | i+1 => mkAnd (mkLE i) (mkResultType i)

  mkType (i : Nat) : Expr :=
    match i with
    | 0 => mkResultType n
    | i+1 => .forallE `x Nat.mkType (mkAnd (mkType i) (mkLE (n - i - 1))) .default

partial def bench1 (n : Nat) : MetaM Unit := do
  runBench "bench1" n mkBench1

run_meta do
  IO.println "Example (n = 5):"
  let ex ← (← mkBench1 5).getType
  IO.println s!"{← ppExpr ex}"
  for i in [10, 20, 40, 80, 100, 200, 300, 400, 500] do
    bench1 i
