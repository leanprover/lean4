import Lean

/-!
`case` solves goals for synthetic opaque metavariables that a tactic created under binders, in any
order, including goals whose types depend on other goals (`?prf1 : ?inv 13`).
-/

syntax (name := specialTactic) "specialTactic" : tactic

open Lean Meta Elab Tactic in
@[tactic specialTactic]
meta def evalSpecialTactic : Tactic := fun _ => do
  let mv ← getMainGoal
  let .forallE _ hpTy (.forallE _ hinvTy _ _) _ := (← mv.getType) | failure
  let prf ←
    withLocalDecl `hp .default hpTy fun hp => do
    withLocalDecl `hinv .default hinvTy fun hinv => do
    let n ← mkFreshExprMVar (mkConst ``Nat) .natural `n
    let inv ← mkFreshExprSyntheticOpaqueMVar (← mkArrow (mkConst ``Nat) (mkSort 0)) `inv
    let prf₁ ← mkFreshExprSyntheticOpaqueMVar (mkApp inv (mkNatLit 13)) `prf1
    let hq := mkApp2 hinv inv prf₁
    let prf₂ ← mkFreshExprSyntheticOpaqueMVar (← mkEq n (mkNatLit 42)) `prf2
    replaceMainGoal <| [n, inv, prf₁, prf₂].map (·.mvarId!)
    mkLambdaFVars #[hp, hinv] (mkApp3 hp n prf₂ hq)
  mv.assign prf

example  : (hp : ∀m, m = 42 → q → p) → (hinv : ∀ (inv : Nat → Prop), inv 13 → q) → p := by
  specialTactic
  -- intro hp
  -- let ?n : Nat
  -- let ?inv : Nat → Prop
  -- let ?prf1 : inv 13
  -- let hinv : inv 13 := ?prf1
  -- let ?prf2 : n = 42
  -- exact hp ?n ?prf2
  case prf2 => rfl
  case inv => exact fun _ => True
  case prf1 => grind
