import Lean
open Lean Meta

/-!
Regression test for `instantiateMVars` on a chain of delayed-assigned
metavariables whose binder domains share a subterm that carries a free
variable (`c`) but none of the abstracted binders.

Introducing `n` binders one at a time builds an `n`-long delayed-assignment
chain. Each binder domain `sₖ = sₖ` shares the accumulator `sₖ = 1 + sₖ₋₁`
anchored at the context-local `c`, so the closed proof is linear in `n` after
hash-consing. Collapsing the chain must stay linear: the shared, binder-free
domains are returned unchanged at every depth via a per-pointer fast path.

This checks correctness of that fast path: the materialized proof must be
type-correct (a wrongly skipped substitution would leave a dangling variable).
-/

def buildAndCheck (n : Nat) : MetaM Bool :=
  withLocalDeclD `c (mkConst ``Nat) fun c => do
    let one := mkNatLit 1
    let mut s := mkApp2 (mkConst ``Nat.add) one c
    let mut domains : Array Expr := #[]
    for _ in [0:n] do
      domains := domains.push (← mkEq s s)
      s := mkApp2 (mkConst ``Nat.add) one s
    let sn := s
    let type ← domains.foldrM (fun d acc => mkArrow d acc) (← mkEq sn sn)
    let mv ← mkFreshExprSyntheticOpaqueMVar type
    let mut g := mv.mvarId!
    for _ in [0:n] do
      let (_, g') ← g.intro1
      g := g'
    g.assign (← g.withContext (mkEqRefl sn))
    let prf ← instantiateMVars (mkMVar mv.mvarId!)
    Meta.check prf
    isTypeCorrect prf

#eval do
  let ok ← buildAndCheck 400
  IO.println s!"type correct: {ok}"
