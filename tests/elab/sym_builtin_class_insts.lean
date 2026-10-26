import Lean
/-!
`Sym.synthInstanceMeta?` answers the algebraic structure queries of `Sym.Arith` classification for
`Int`, `Nat` and `Rat`, and the operator queries for `Rat`, from a table. The answers must be the
ones of type class resolution.
-/
open Lean Meta Elab Command

def checkQuery (e : Expr) : MetaM Unit := do
  let r₁ ← withNewMCtxDepth do
    let r ← Sym.synthInstanceMeta? e
    return (r, ← instantiateMVars e)
  let r₂ ← withNewMCtxDepth do
    let r ← catchInternalId isDefEqStuckExceptionId (synthInstance? e) fun _ => pure none
    return (r, ← instantiateMVars e)
  unless r₁ == r₂ do
    throwError "mismatch for {e}: {r₁.1} {r₁.2} vs {r₂.1} {r₂.2}"

elab "#check_builtin_class_insts" : command => liftTermElabM do
  let z := [Level.zero]
  let app (n : Name) (args : Array Expr) := mkAppN (mkConst n z) args
  let int := mkConst ``Int
  let nat := mkConst ``Nat
  let srI := app ``Grind.Ring.toSemiring #[int, app ``Grind.CommRing.toRing #[int, mkConst ``Grind.instCommRingInt]]
  let nmI := app ``Grind.Semiring.toNatModule #[int, app ``Grind.CommSemiring.toSemiring #[int,
    app ``Grind.CommRing.toCommSemiring #[int, mkConst ``Grind.instCommRingInt]]]
  let srN := app ``Grind.CommSemiring.toSemiring #[nat, mkConst ``Grind.instCommSemiringNat]
  let nmN := app ``Grind.Semiring.toNatModule #[nat, srN]
  let some preI ← synthInstance? (app ``Std.IsPreorder #[int, mkConst ``Int.instLEInt]) | unreachable!
  let some preN ← synthInstance? (app ``Std.IsPreorder #[nat, mkConst ``instLENat]) | unreachable!
  for (t, sr, nm, le, lt, pre) in [(int, srI, nmI, mkConst ``Int.instLEInt, mkConst ``Int.instLTInt, preI),
      (nat, srN, nmN, mkConst ``instLENat, mkConst ``instLTNat, preN)] do
    for c in [``Grind.CommRing, ``Grind.Ring, ``Grind.Field, ``Grind.CommSemiring, ``Grind.Semiring, ``Grind.NatModule, ``NatCast, ``Max, ``Dvd] do
      checkQuery (app c #[t])
    checkQuery (app ``Grind.NoNatZeroDivisors #[t, nm])
    checkQuery (app ``Grind.AddRightCancel #[t, ← synthInstance (app ``Add #[t])])
    for c in [``Std.IsPreorder, ``Std.IsPartialOrder, ``Std.IsLinearPreorder, ``Std.IsLinearOrder] do
      checkQuery (app c #[t, le])
    checkQuery (app ``Std.LawfulOrderLT #[t, lt, le])
    checkQuery (app ``Grind.OrderedRing #[t, sr, le, lt, pre])
    checkQuery (app ``Grind.IsCharP #[t, sr, ← mkFreshExprMVar nat])
    let cs ← mkFreshExprMVar (app ``Grind.CommSemiring #[t])
    checkQuery (app ``Grind.PowIdentity #[t, cs, ← mkFreshExprMVar nat])
  for c in [``Grind.CommRing, ``Grind.Ring, ``Grind.CommSemiring, ``Grind.Semiring] do
    checkQuery (app c #[mkConst ``Bool])
    checkQuery (app c #[mkSort 0])
  -- `Rat`
  let rat := mkConst ``Rat
  let crR := app ``Grind.Field.toCommRing #[rat, mkConst ``Grind.instFieldRat]
  let srR := app ``Grind.Ring.toSemiring #[rat, app ``Grind.CommRing.toRing #[rat, crR]]
  let nmR := app ``Grind.Semiring.toNatModule #[rat, app ``Grind.CommSemiring.toSemiring #[rat,
    app ``Grind.CommRing.toCommSemiring #[rat, crR]]]
  let leR := mkConst ``Rat.instLE
  let ltR := mkConst ``Rat.instLT
  let some preR ← synthInstance? (app ``Std.IsPreorder #[rat, leR]) | unreachable!
  for c in [``Grind.CommRing, ``Grind.Ring, ``Grind.Field, ``Grind.CommSemiring, ``Grind.Semiring, ``Grind.NatModule,
      ``NatCast, ``IntCast, ``Max, ``LE, ``LT, ``Neg, ``Inv] do
    checkQuery (app c #[rat])
  checkQuery (app ``Grind.NoNatZeroDivisors #[rat, nmR])
  for c in [``Std.IsPreorder, ``Std.IsPartialOrder, ``Std.IsLinearPreorder, ``Std.IsLinearOrder] do
    checkQuery (app c #[rat, leR])
  checkQuery (app ``Std.LawfulOrderLT #[rat, ltR, leR])
  checkQuery (app ``Grind.OrderedRing #[rat, srR, leR, ltR, preR])
  checkQuery (app ``Grind.IsCharP #[rat, srR, ← mkFreshExprMVar (mkConst ``Nat)])
  let cs ← mkFreshExprMVar (app ``Grind.CommSemiring #[rat])
  checkQuery (app ``Grind.PowIdentity #[rat, cs, ← mkFreshExprMVar (mkConst ``Nat)])
  let us := [Level.zero, Level.zero, Level.zero]
  for c in [``HAdd, ``HSub, ``HMul, ``HDiv] do
    checkQuery (mkApp3 (mkConst c us) rat rat rat)
  checkQuery (mkApp3 (mkConst ``HPow us) rat (mkConst ``Nat) rat)
  for n in [0, 1, 7] do
    checkQuery (mkApp2 (mkConst ``OfNat [Level.zero]) rat (mkRawNatLit n))
  logInfo "ok"

/-- info: ok -/
#guard_msgs in
#check_builtin_class_insts
