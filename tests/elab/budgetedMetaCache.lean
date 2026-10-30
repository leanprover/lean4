module

import Lean

/-!
Tests budgeted type-inference caching for #15985 while WHNF, definitional equality, and
unit-like caches retain structural equality.
-/

open Lean Meta

private def check (ok : Bool) (msg : String) : MetaM Unit :=
  unless ok do throwError msg

@[noinline] private def chain (fn : Expr) (n : Nat) : IO Expr := do
  let r ← IO.mkRef (mkBVar 0)
  for _ in [:n] do r.modify fun e => mkApp fn e
  r.get

run_meta do
  let nat := mkConst ``Nat
  let x := mkLambda `x .default nat (mkBVar 0)
  let y := mkLambda `y .implicit nat (mkBVar 0)
  let kx ← mkExprConfigCacheKey x
  let ky ← mkExprConfigCacheKey y
  check ((← BudgetedBEq.beq kx ky 1) == .false) "expression keys must compare binder information"
  let infer : InferTypeCache := ({} : InferTypeCache).insert kx nat
  let result ← infer.find? ky (fun _ => throwError "inequality must not evict")
  check result.isNone "binder differences must miss in inferType cache"
  let whnf : WhnfCache := ({} : WhnfCache).insert kx x
  check (whnf.find? ky).isNone "binder differences must miss in whnf cache"
  let unitLike : IsUnitLikeCache := ({} : IsUnitLikeCache).insert kx false
  check (unitLike.find? kx == some false) "cached false must be a hit"
  let kx ← mkDefEqCacheKey x nat
  let ky ← mkDefEqCacheKey y nat
  let defEq : DefEqCache := ({} : DefEqCache).insert kx false
  check (defEq.find? ky == some false) "defeq cache must ignore binder information"
  let fn := mkConst `f
  let a ← chain fn 128
  let b ← chain fn 128
  let ka ← mkExprConfigCacheKey a
  let kb ← mkExprConfigCacheKey b
  let infer : InferTypeCache := ({} : InferTypeCache).insert ka nat
  let updated ← IO.mkRef infer
  let result ← infer.find? kb (fun c => updated.set c) 64
  check result.isNone "inferType comparison must exhaust"
  let result ← (← updated.get).find? ka (fun _ => throwError "entry should be absent") 0
  check result.isNone "exhaustion must evict the inferType entry"
  let whnf : WhnfCache := ({} : WhnfCache).insert ka a
  check (whnf.find? kb == some a) "whnf must retain large structural hits"
  let unitLike : IsUnitLikeCache := ({} : IsUnitLikeCache).insert ka false
  check (unitLike.find? kb == some false) "unit-like cache must retain large structural hits"
  let ka ← mkDefEqCacheKey a nat
  let kb ← mkDefEqCacheKey b nat
  let defEq : DefEqCache := ({} : DefEqCache).insert ka true
  check (defEq.find? kb == some true) "defeq must retain large structural hits"
  let ka ← mkExprConfigCacheKey a
  let kc ← withConfig (fun c => { c with zeta := !c.zeta }) <| mkExprConfigCacheKey b
  check ((← BudgetedBEq.beq ka kc 0) == .false) "configuration must be checked first"
