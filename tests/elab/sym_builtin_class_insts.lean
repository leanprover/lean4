import Lean
/-!
`Sym.synthInstanceMeta?` answers the algebraic structure queries of `Sym.Arith` classification for
`Int` and `Nat` from a table. The answers must be the ones of type class resolution, including the
assignment of output parameters.
-/
open Lean Meta Elab Command

/-- Compares both answers for the query `mk` builds, with its output metavariables created at the new depth. -/
def checkQueryWith (mk : MetaM Expr) : MetaM (Option Expr × Expr) := do
  let r₁ ← withNewMCtxDepth do
    let e ← mk
    let r ← Sym.synthInstanceMeta? e
    return (r, (← abstractMVars (← instantiateMVars e)).expr)
  let r₂ ← withNewMCtxDepth do
    let e ← mk
    let r ← catchInternalId isDefEqStuckExceptionId (synthInstance? e) fun _ => pure none
    return (r, (← abstractMVars (← instantiateMVars e)).expr)
  unless r₁ == r₂ do
    throwError "mismatch: {r₁.1} {r₁.2} vs {r₂.1} {r₂.2}"
  return r₁

def checkQuery (e : Expr) : MetaM Unit := discard <| checkQueryWith (pure e)

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
    let (inst?, e) ← checkQueryWith do return app ``Grind.IsCharP #[t, sr, ← mkFreshExprMVar nat]
    unless inst?.isSome && e.appArg!.nat? == some 0 do
      throwError "expected `IsCharP {t} 0`, got {inst?} for {e}"
    discard <| checkQueryWith do
      return app ``Grind.PowIdentity #[t, ← mkFreshExprMVar (app ``Grind.CommSemiring #[t]), ← mkFreshExprMVar nat]
  for c in [``Grind.CommRing, ``Grind.Ring, ``Grind.CommSemiring, ``Grind.Semiring] do
    checkQuery (app c #[mkSort 0])
  logInfo "ok"

/-- info: ok -/
#guard_msgs in
#check_builtin_class_insts
