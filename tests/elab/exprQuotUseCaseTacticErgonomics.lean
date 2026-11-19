import Lean

/-!
# Goal-directed `TacticM` automation: `whileGoals`, `andThenSubgoals`, and inline refutation

- `typecheck` proves typing derivations of a small lambda calculus by dispatching on the main goal
  with `` `(expr| ...) `` patterns and `Tactic.whileGoals` / `Tactic.andThenSubgoals`.
- `refute_intros` introduces hypotheses one at a time via `whileGoals` and closes the goal inline
  using `MVarId.firstHyp?` + `` `(expr/reducible| ...) `` as soon as the newest hypothesis is
  contradictory (`x ≠ x`, distinct constructors, `decide`-refutable closed prop, or `p` vs `¬ p`).
-/

namespace TacticErgonomics

inductive Ty where
  | nat | bool | arr (a b : Ty)

inductive Tm where
  | lit (n : Nat) | tt | var (i : Nat) | add (a b : Tm) | ite (c t e : Tm)
  | lam (a : Ty) (b : Tm) | app (f x : Tm)

inductive HasType : List Ty → Tm → Ty → Prop
  | lit : HasType Γ (.lit n) .nat
  | tt : HasType Γ .tt .bool
  | var : Γ[i]? = some τ → HasType Γ (.var i) τ
  | add : HasType Γ a .nat → HasType Γ b .nat → HasType Γ (.add a b) .nat
  | ite : HasType Γ c .bool → HasType Γ t τ → HasType Γ e τ → HasType Γ (.ite c t e) τ
  | lam : HasType (α :: Γ) b β → HasType Γ (.lam α b) (.arr α β)
  | app : HasType Γ f (.arr α β) → HasType Γ x α → HasType Γ (.app f x) β

theorem HasType.congr_tm {Γ : List Ty} {t t' : Tm} {τ : Ty}
    (h : t = t') (ht : HasType Γ t' τ) : HasType Γ t τ :=
  h ▸ ht

def double : Tm := .lam .nat (.add (.var 0) (.var 0))
def choose : Tm := .lam .bool (.lam .nat (.ite (.var 1) (.var 0) (.lit 0)))

section Tactics
open Lean Meta Elab Tactic

/-- Unfolds a `let`-bound or global term definition `t` inside `HasType Γ t τ`. -/
def unfoldTmGoal (g : MVarId) : MetaM MVarId := g.withContext do
  let `(expr| HasType ?γ ?t ?τ) ← g.getType
    | throwError "unfoldTmGoal: expected HasType goal"
  if let .fvar fv := t.getAppFn then
    if let some v ← fv.getValue? then
      return ← g.replaceTargetDefEq (← `(expr| HasType $γ $(v.betaRev t.getAppRevArgs) $τ))
  let some f := t.getAppFn.constName?
    | throwError "unfoldTmGoal: cannot unfold{indentExpr t}"
  let r ← Lean.Meta.unfold t f
  if r.expr == t then
    throwError "unfoldTmGoal: cannot unfold{indentExpr t}"
  match r.proof? with
  | none => g.replaceTargetDefEq (← `(expr| HasType $γ $(r.expr) $τ))
  | some pf =>
    let newG ← mkFreshExprSyntheticOpaqueMVar (← `(expr| HasType $γ $(r.expr) $τ))
    g.assign (mkAppN (mkConst ``HasType.congr_tm) #[γ, t, r.expr, τ, pf, newG])
    return newG.mvarId!

/-- One `typecheck` step on the main goal. -/
partial def tcStep : TacticM Unit := withMainContext do
  let apply (rule : Name) : TacticM Unit := do
    replaceMainGoal (← (← getMainGoal).apply (← mkConstWithFreshMVarLevels rule))
  match ← getMainTarget with
  | `(expr| HasType _ (.lit _) _) => apply ``HasType.lit
  | `(expr| HasType _ .tt _) => apply ``HasType.tt
  | `(expr| HasType _ (.var _) _) =>
    andThenSubgoals (apply ``HasType.var) (first := do (← getMainGoal).refl)
  | `(expr| HasType _ (.add _ _) _) => apply ``HasType.add
  | `(expr| HasType _ (.ite _ _ _) _) => apply ``HasType.ite
  | `(expr| HasType _ (.lam _ _) _) => apply ``HasType.lam
  | `(expr| HasType _ (.app _ _) _) =>
    -- `HasType.app` leaves `?α` open; checking the function first assigns it, and the
    -- assigned `?α` goal is then skipped instead of being dispatched to `rest`.
    andThenSubgoals (apply ``HasType.app) (first := whileGoals tcStep)
  | `(expr| HasType _ _ _) => replaceMainGoal [← unfoldTmGoal (← getMainGoal)]
  | tgt => throwError "typecheck: unexpected goal{indentExpr tgt}"

/-- `typecheck` proves every open `HasType` goal. -/
elab "typecheck" : tactic => whileGoals tcStep

/-- Single-hypothesis refutation defined inline via `MVarId.firstHyp?` + `expr` quotations. -/
def refuteHyp? (g : MVarId) (h : FVarId) : MetaM Bool := g.withContext do
  let p ← instantiateMVars (← h.getType)
  let tgt ← g.getType
  match p with
  | `(expr/reducible| @Eq _ ?x ?y) =>
    if let (some c₁, some c₂) := (← matchConstructorApp? x, ← matchConstructorApp? y) then
      if c₁.name != c₂.name then
        g.assign (← mkNoConfusion tgt (.fvar h))
        return true
  | `(expr/reducible| ¬ (@Eq _ ?x $x)) =>
    g.assign (← mkAbsurd tgt (← mkEqRefl x) (.fvar h))
    return true
  | _ => pure ()
  if !p.hasFVar && !p.hasMVar then
    if let some prf ← observing? (mkDecideProof (mkNot p)) then
      g.assign (← mkAbsurd tgt (.fvar h) prf)
      return true
  let res? ← g.firstHyp? (except := [.fvar h]) fun h' ty => do
    match p, ty with
    | `(expr/reducible| ¬ (?q : Prop)), `(expr/reducible| $q) =>
      g.assign (← mkAbsurd tgt h' (.fvar h))
    | _, `(expr/reducible| ¬ $p) =>
      g.assign (← mkAbsurd tgt (.fvar h) h')
    | _, _ => failure
  return res?.isSome

/-- `refute_intros`: introduce hypotheses until the newest one refutes the goal. -/
elab "refute_intros" : tactic => whileGoals do
  let (h, g) ← (← getMainGoal).intro1
  replaceMainGoal (if ← refuteHyp? g h then [] else [g])

end Tactics

/-! ## Type checking -/

example : HasType [] (.app double (.lit 2)) .nat := by
  typecheck

example : HasType [] choose (.arr .bool (.arr .nat .nat)) := by
  typecheck

example : let t := Tm.app double (.app double (.lit 1)); HasType [] t .nat := by
  intro t
  typecheck

/-! ## Path-condition pruning -/

example (P : Prop) (n : Nat) : n ≠ n → P := by refute_intros
example (P : Prop) : some 1 = none → P := by refute_intros
example (P : Prop) : (3 : Nat) = 4 → P := by refute_intros
-- The newest hypothesis `b = true` is refuted by the *older* `¬b = true`.
example (P : Prop) (b : Bool) : ¬b = true → (n : Nat) → b = true → P := by refute_intros

end TacticErgonomics
