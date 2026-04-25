import Lean.Meta.Sym

open Lean Meta Sym

/-! ## Level commutativity: `max u v` vs `max v u` with concrete params -/

/--
info: rule.apply succeeds: max u v matches max v u
-/
#guard_msgs in
#eval show MetaM Unit from do
  let u := Level.param `u
  let v := Level.param `v
  let maxUV := Level.max u v
  let maxVU := Level.max v u
  let proof := mkApp2 (mkConst ``Eq.refl [maxUV.succ]) (mkSort maxUV) (mkSort maxUV)
  let rule ← mkBackwardRuleFromExpr proof (levelParams := [`u, `v])
  let goalType := mkApp3 (mkConst ``Eq [maxVU.succ]) (mkSort maxVU) (mkSort maxVU) (mkSort maxVU)
  let r ← SymM.run do
    let mvar ← mkFreshExprMVar goalType
    let mvarId ← preprocessMVar mvar.mvarId!
    rule.apply mvarId
  match r with
  | .goals _ => logInfo "rule.apply succeeds: max u v matches max v u"
  | .failed  => logInfo "rule.apply FAILED: max u v did not match max v u"

/-! ## `tryApproxMaxMax`: pattern `max _uvar 1` matching target `max 1 u` -/

axiom lvlAxiom : ∀ (α : Sort (max u 1)), α → α

/--
info: pattern match succeeded
-/
#guard_msgs in
#eval show MetaM Unit from do
  let pat ← mkPatternFromDecl ``lvlAxiom
  -- Target has `max 1 u` (swapped from pattern's `max u 1`)
  let u := Level.param `u
  let lvl := Level.max (.succ .zero) u  -- max 1 u
  let targetType := Expr.forallE `α (.sort lvl) (Expr.forallE `a (.bvar 0) (.bvar 1) .default) .implicit
  let r ← SymM.run do
    pat.match? targetType
  match r with
  | some _ => logInfo "pattern match succeeded"
  | none   => logInfo "pattern match FAILED"
