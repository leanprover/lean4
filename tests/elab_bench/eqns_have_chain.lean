module

import Lean

/-!
Benchmark equation generation for a match below a long chain of shared values (#16122).
Every value uses the preceding value twice, so zeta expansion would be exponential. The resulting
equations must retain the chain inside its original binding and have size linear in its length.
Also cover nested binding values: checking each complete value at every enclosing scope would
repeatedly traverse the same inner telescope.
-/

open Lean Meta

set_option maxHeartbeats 400000
set_option maxRecDepth 100000

-- Opaque applications keep reduction costs independent of the chain's expanded size.
private opaque combine (a b : Nat) : Nat := a + b

private def chainTail (x a : Nat) : Nat :=
  match x with
  | 0 => a
  | n + 1 => combine (combine a a) n

private def makeChainDefinition (n : Nat) : MetaM Name := do
  let name ← mkFreshUserName `eqnsHaveChain
  let nat := mkConst ``Nat
  let arrow ← mkArrow nat nat
  let type ← mkArrow arrow arrow
  let value ← withLocalDeclD `f arrow fun f =>
    withLocalDeclD `x nat fun x => do
      let .lam _ _ (.lam _ _ template _) _ := (← getConstInfoDefn ``chainTail).value
        | throwError "unexpected chain template"
      let mut body := template.instantiateRev #[x, mkBVar 0]
      for _ in [:n] do
        body := mkLet `a nat (mkApp2 (mkConst ``combine) (mkBVar 0) (mkBVar 0)) body true
      body := mkLet `a nat (mkApp f x) body true
      body := mkLet `result nat body (mkApp2 (mkConst ``combine) (mkBVar 0) (mkBVar 0)) true
      mkLambdaFVars #[f, x] body
  let hints := ReducibilityHints.regular (getMaxHeight (← getEnv) value + 1)
  addDecl <| .defnDecl { name, levelParams := [], type, value, hints, safety := .safe }
  enableRealizationsForConst name
  return name

private def makeNestedDefinition (n : Nat) : MetaM Name := do
  let name ← mkFreshUserName `eqnsNestedHave
  let nat := mkConst ``Nat
  let type ← mkArrow nat nat
  let value ← withLocalDeclD `x nat fun x => do
    let .lam _ _ (.lam _ _ template _) _ := (← getConstInfoDefn ``chainTail).value
      | throwError "unexpected chain template"
    let mut body := template.instantiateRev #[x, mkNatLit 0]
    for _ in [:n] do
      body := mkHave `a nat body (mkApp2 (mkConst ``combine) (mkBVar 0) (mkBVar 0))
    mkLambdaFVars #[x] body
  let hints := ReducibilityHints.regular (getMaxHeight (← getEnv) value + 1)
  addDecl <| .defnDecl { name, levelParams := [], type, value, hints, safety := .safe }
  enableRealizationsForConst name
  return name

run_meta do
  let bench := (← IO.getEnv "TEST_BENCH") == some "1"
  for n in (if bench then [200, 400, 800] else [25]) do
    let name ← makeChainDefinition n
    let start ← IO.monoNanosNow
    let some eqns ← getEqnsFor? name | throwError "missing equations"
    let infos ← eqns.mapM getConstInfo
    unless ((← getEnv).toKernelEnv.find? name).isSome do
      throwError "missing definition after checking equations"
    let stop ← IO.monoNanosNow
    if bench then
      IO.println s!"measurement: eqns_have_chain_{n} {(stop - start).toFloat / 1e9} s"
    unless eqns.size == 2 do throwError "expected two equations, got {eqns.size}"
    for info in infos do
      forallTelescope info.type fun _ body => do
        let some (_, _, .letE _ _ inner _ true) := body.eq?
          | throwError "outer binding was lost"
        let mut value := inner
        let mut count : Nat := 0
        while let .letE _ _ _ body true := value do
          count := count + 1
          value := body
        unless count == n + 1 do
          throwError "expected {n + 1} nested bindings, got {count}"
        unless (← body.numObjs) ≤ 32 * n + 256 do
          throwError "equation exceeded the size bound for {n} bindings"

run_meta do
  let bench := (← IO.getEnv "TEST_BENCH") == some "1"
  for n in (if bench then [200, 400, 800] else [25]) do
    let name ← makeNestedDefinition n
    let start ← IO.monoNanosNow
    let some eqns ← getEqnsFor? name | throwError "missing equations"
    let infos ← eqns.mapM getConstInfo
    let stop ← IO.monoNanosNow
    if bench then
      IO.println s!"measurement: eqns_nested_have_{n} {(stop - start).toFloat / 1e9} s"
    if eqns.size != 2 then throwError "expected two equations, got {eqns.size}"
    for info in infos do
      forallTelescope info.type fun _ body => do
        let some (_, _, rhs) := body.eq? | throwError "expected an equation"
        let mut value := rhs
        let mut count := 0
        while let .letE _ _ inner _ true := value do
          count := count + 1
          value := inner
        if count != n then throwError "expected {n} nested bindings, got {count}"
        if (← rhs.numObjs) > 32 * n + 256 then
          throwError "equation exceeded the size bound for {n} bindings"
