module

public import Lean

/-!
Spike A tests verifying `exprQuot` auxiliary pattern constants under the Lean module system
(`public meta def`, `private meta def`, `@[expose] public def`, non-exposed `public def`,
and `meta section`).
-/

open Lean Meta

namespace ExprQuotSpikeAModule

public meta def pubMetaMatch (e : Expr) : MetaM Bool :=
  match e with
  | `(expr| ?a + ?b) => return a == b
  | _ => return false

private meta def privMetaMatch (e : Expr) : MetaM (Option Expr) :=
  match e with
  | `(expr/defeq| 0 + ?x) => return some x
  | _ => return none

@[expose] public def exposedNonMetaMatch (e : Expr) : MetaM Nat := do
  if let `(expr| ?a * ?b) := e then
    let _ := (a, b)
    return 1
  else
    return 0

public def publicNonExposedMatch (e : Expr) : MetaM Nat :=
  match (modulo := reducible) e with
  | `(expr| ?a + ?b) => let _ := (a, b); return 2
  | _ => return 3

meta section

def insideMetaSection (e : Expr) : MetaM Nat := do
  let mut count := 0
  match e with
  | `(expr| ?a + ?b) =>
    let _ := (a, b)
    count := count + 1
  | _ => count := count + 10
  return count

end

#eval show MetaM Unit from do
  let one := mkNatLit 1
  let add11 := mkNatAdd one one
  assert! (← pubMetaMatch add11)
  assert! (← privMetaMatch (mkNatAdd (mkNatLit 0) one)) == some one
  assert! (← exposedNonMetaMatch (mkNatMul one one)) == 1
  assert! (← publicNonExposedMatch add11) == 2
  assert! (← insideMetaSection add11) == 1

end ExprQuotSpikeAModule
