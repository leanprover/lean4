module
public meta import Lean

/-!
Regression tests for the instance canonicalization cache bug exposed by #15071.
Visiting an instance as an ordinary term must not affect its canonicalization as an
instance argument, or vice versa, in either value or type contexts.
-/

open Lean Meta Sym

opaque Box {α : Type} (a : α) : Type

meta def checkInstanceCache (insideType instanceFirst : Bool) : MetaM Unit := do
  let nat := mkConst ``Nat
  let oldInst := mkApp2 (mkConst ``instBEqOfDecidableEq [0]) nat (mkConst ``instDecidableEqNat)
  let newInst ← Meta.synthInstance (mkApp (mkConst ``BEq [0]) nat)
  let countOld := mkApp4 (mkConst ``List.count [0]) nat oldInst (mkNatLit 0)
    (mkApp (mkConst ``List.nil [0]) nat)
  let countNew := mkApp4 (mkConst ``List.count [0]) nat newInst (mkNatLit 0)
    (mkApp (mkConst ``List.nil [0]) nat)
  let wrap (e : Expr) : MetaM Expr := do
    if insideType then
      return mkApp (mkConst ``List [0]) (mkApp2 (mkConst ``Box) (← inferType e) e)
    else
      return e
  let ordinary ← wrap oldInst
  let instanceArg ← wrap countOld
  let canonicalInstanceArg ← wrap countNew
  let expectedOrdinary ← SymM.run <| Sym.canon ordinary
  let expectedInstanceArg ← SymM.run <| Sym.canon canonicalInstanceArg
  SymM.run do
    let checkOrdinary : SymM Unit := do
      unless (← Sym.canon ordinary) == expectedOrdinary do
        throwError "ordinary-term canonicalization depends on visit order (insideType := {insideType})"
    let checkInstance : SymM Unit := do
      unless (← Sym.canon instanceArg) == expectedInstanceArg do
        throwError "instance canonicalization depends on visit order (insideType := {insideType})"
    if instanceFirst then
      checkInstance
      checkOrdinary
    else
      checkOrdinary
      checkInstance

run_meta checkInstanceCache false false
run_meta checkInstanceCache false true
run_meta checkInstanceCache true false
run_meta checkInstanceCache true true

example (a n : Nat) : List.count a (List.range n) ≤ 1 := by
  grind only [List.count_range]

example (a n : Nat) : List.count a (List.range n) = if a < n then 1 else 0 := by
  grind
