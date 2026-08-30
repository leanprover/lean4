import Lean
/-!
# Tests of the `Lean.Meta.abstractMVars` procedure
-/

open Lean Meta

/-!
The following example used to abstract `levelMVar` even though it was assigned.
The issue was that the procedure failed to instantiateMVars in the types of metavariables.

Reported on Zulip: https://leanprover.zulipchat.com/#narrow/channel/239415-metaprogramming-.2F-tactics/topic/.60abstractMVars.60.20not.20instantiating.20level.20mvars/near/541918246
-/

/-- info: [] -/
#guard_msgs in
run_meta
  let levelMVar ← mkFreshLevelMVar
  let mvar ← mkFreshExprMVar (some (mkSort levelMVar))
  discard <| isDefEq (mkSort levelMVar) (mkSort (mkLevelParam `u))
  let mvar ← instantiateMVars mvar
  let abstractResult ← abstractMVars mvar
  Lean.logInfo m!"{abstractResult.paramNames}"

/-!
Test from the `abstractMVars` docstring.

f.{?u} ?m1`, where `?m1 : ?m2 Nat` and `?m2 : Type -> Type
-/
namespace DocStringEx
def f.{v} (α : Type → Type v) : α Nat → Nat := fun _ => 0
deriving instance Repr for AbstractMVarsResult
set_option pp.funBinderTypes true
set_option pp.mvars.levels false
/--
info: [_]
[_abstMVar.1]
[?m.1 : Type → Type _, ?m.2 : ?m.1 Nat]
fun (x_1 : Type → Type _abstMVar.1) (x_2 : x_1 Nat) => f x_1 x_2
-/
#guard_msgs in
run_meta
  let u ← mkFreshLevelMVar
  let m1 ← mkFreshExprMVar (Expr.forallE `a (.sort .one) (.sort u.succ) .default)
  let m2 ← mkFreshExprMVar (Expr.app m1 (.const ``Nat []))
  let e := mkAppN (.const ``f [u]) #[m1, m2]
  let r ← abstractMVars e
  let exprArgs ← r.exprArgs.mapM fun m => return m!"{m} : {← inferType m}"
  logInfo m!"{r.lmvars}\n{r.paramNames}\n{exprArgs}\n{r.expr}"

end DocStringEx

/-!
Test demonstrating `MVarId.abstractMVars`.
-/
elab "abstract_mvars" : tactic =>
  Elab.Tactic.liftMetaTactic1 fun g => g.abstractMVars

/--
info: Try this:
  [apply] have this := fun (x : Fin 22) => x;
  Function.const (Fin 22 → Fin 22) trivial this
---
trace: case refine_1
⊢ (n : Nat) → Fin n → Fin n
-/
#guard_msgs in
set_option pp.mvars.anonymous false in
set_option pp.funBinderTypes true in
example : True := by?
  have : Fin ?n → Fin ?n := ?_
  rotate_right
  · abstract_mvars
    trace_state
    intro n
    exact fun x => x
  exact Function.const _ trivial this
  exact 22

/-!
Checking that we follow the types of free variables when determining fixed metavariables.
If we didn't do this check, then we would see this erroneously abstract `?α`.
Instead, it only abstracts `?p`.
-/
/--
trace: a : ?α
b : a = a
⊢ ∀ (p : Sort _) (a_1 : p), b = b
---
warning: declaration uses `sorry`
-/
#guard_msgs in
set_option pp.mvars.anonymous false in
example : True := by
  have a : ?α := sorry
  have b : a = a := rfl
  have : ?p → b = b := by
    abstract_mvars
    trace_state
    intro p h
    rfl
  case p => exact False
  case α => exact Nat
  trivial

/-!
Test demonstrating a Hindley-Milner-like `let` abstraction procedure
using `abstractMVarsWithType`. (The results leave something to be desired, but it's just a demo.)

Currently `abstractMVars` doesn't do any special processing with delayed assignments.
Possibly by tracing delayed assignments, it could produce a least-dependent most-general type.
-/

syntax withPosition("let_abs " letDecl) : tactic

open Elab Tactic in
elab_rules : tactic
  | `(tactic| let_abs $n:ident $[$bs:letIdBinder]* $[: $ty?]? := $e) =>
    withMainContext do
      let r ← runTermElab do
        let (ty, e) ← Term.elabBinders bs fun xs => do
          let ty ← if let some ty := ty? then Term.elabTerm ty none else mkFreshTypeMVar
          let e ← Term.elabTermEnsuringType e ty
          Term.synthesizeSyntheticMVars (ignoreStuckTC := true) (postpone := .no)
          return (← mkForallFVars xs ty, ← mkLambdaFVars xs e)
        abstractMVarsWithType ty e (levels := false) (inferNames := true) (binderInfo := .implicit)
      let bis ← forallBoundedTelescope r.type r.numMVars fun xs _ => do
        xs.mapM fun x => do
          if (← isClass? (← x.fvarId!.getType)).isSome then
            pure (some BinderInfo.instImplicit)
          else
            pure none
      let type := r.type.updateForallBinderInfos bis.toList
      let g ← popMainGoal
      withLetDecl n.getId type r.expr fun fvar => do
        let g' ← mkFreshExprSyntheticOpaqueMVar (← g.getType) (← g.getTag)
        g.assign <| ← mkLetFVars #[fvar] g'
        pushGoal g'.mvarId!

/--
trace: f : {α : Type _} → [x_2 : Option α → α → BEq α] → [x_3 : Option α → α → Inhabited α] → Option α → α → Bool :=
  fun {α} {x_2} {x_3} x y => x.get! == y
⊢ True
-/
#guard_msgs in
set_option pp.mvars.anonymous false in
example : True := by
  let_abs f := fun x y => Option.get! x == y
  trace_state
  -- Despite the weird instances, at least it still can be instantiated:
  have : f (some true) true = true := rfl
  trivial
