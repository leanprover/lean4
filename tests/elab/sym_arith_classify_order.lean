import Lean

/-!
# Tests for `Sym.Arith.classifyOrder?`

The order-instance classification (`LE`, `IsPreorder`, `LT`, `LawfulOrderLT`,
`IsPartialOrder`, `IsLinearPreorder`, `OrderedRing`, link to the ring id) lives in
`Sym.Arith` and is cached for the whole `SymM` run.
-/

open Lean Meta Sym Arith

def summary (type : Expr) : SymM String := do
  let some id ← classifyOrder? type | return "none"
  let o := (← getArithState).orders[id]!
  return s!"id={o.id} lt={o.ltInst?.isSome} partial={o.isPartialInst?.isSome} linear={o.isLinearPreInst?.isSome} lawfulLT={o.lawfulOrderLTInst?.isSome} ring={o.ringId?} commRing={o.isCommRing} orderedRing={o.orderedRingInst?.isSome}"

/-- info: id=0 lt=true partial=true linear=true lawfulLT=true ring=(some 0) commRing=true orderedRing=true -/
#guard_msgs in
run_meta SymM.run do
  logInfo (← summary (mkConst ``Int))

-- `Nat` is a `CommSemiring`, not a ring, so there is no ring link and no `OrderedRing`.
/-- info: id=0 lt=true partial=true linear=true lawfulLT=true ring=none commRing=false orderedRing=false -/
#guard_msgs in
run_meta SymM.run do
  logInfo (← summary (mkConst ``Nat))

-- No `LE` instance.
/-- info: none -/
#guard_msgs in
run_meta SymM.run do
  logInfo (← summary (.forallE `x (mkConst ``Nat) (mkConst ``Nat) .default))

-- Classification is cached: the same type gets the same id, and a second type gets the next one.
/-- info: true, true -/
#guard_msgs in
run_meta SymM.run do
  let some id₁ ← classifyOrder? (mkConst ``Int) | unreachable!
  let some id₂ ← classifyOrder? (mkConst ``Int) | unreachable!
  let some id₃ ← classifyOrder? (mkConst ``Nat) | unreachable!
  logInfo m!"{id₁ == id₂}, {id₃ == id₁ + 1}"

-- The canonical `≤`/`<` functions carry the classified instances.
/-- info: LE.le, LT.lt -/
#guard_msgs in
run_meta SymM.run do
  let some id ← classifyOrder? (mkConst ``Int) | unreachable!
  let o := (← getArithState).orders[id]!
  logInfo m!"{o.leFn.getAppFn.constName!}, {o.ltFn?.get!.getAppFn.constName!}"
