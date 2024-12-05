/-
Copyright (c) 2019 Paul-Nicolas Madelaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul-Nicolas Madelaine, Robert Y. Lewis, Mario Carneiro, Gabriel Ebner
-/
prelude
import Lean.Meta.Tactic.NormCast
import Lean.Elab.Tactic.Conv.Simp
import Lean.Elab.ElabRules

/-!
# The `norm_cast` family of tactics.

A full description of the tactic, and the use of each theorem category, can be found at
<https://arxiv.org/abs/2001.10594>.
-/
namespace Lean.Elab.Tactic.NormCast
open Lean Meta Simp NormCast

-- TODO: trace name consistency
builtin_initialize registerTraceClass `Tactic.norm_cast

/-- Proves `a = b` using the given simp set. -/
def proveEqUsing (s : SimpTheorems) (a b : Expr) : MetaM (Option Simp.Result) := do
  let go : SimpM (Option Simp.Result) := do
    let a' ← Simp.simp a
    let b' ← Simp.simp b
    unless ← isDefEq a'.expr b'.expr do return none
    a'.mkEqTrans (← b'.mkEqSymm b)
  withReducible do
    let ctx ← Simp.mkContext
        (simpTheorems := #[s])
        (congrTheorems := ← Meta.getSimpCongrTheorems)
    (go (← Simp.mkDefaultMethods).toMethodsRef ctx).run' {}

/-- Proves `a = b` by simplifying using move and squash lemmas. -/
def proveEqUsingDown (a b : Expr) : MetaM (Option Simp.Result) := do
  withTraceNode `Tactic.norm_cast (return m!"{exceptOptionEmoji ·} proving: {← mkEq a b}") do
  proveEqUsing (← normCastExt.down.getTheorems) a b

/-- Constructs the expression `(e : ty)`. -/
def mkCoe (e : Expr) (ty : Expr) : MetaM Expr := do
  let .some e' ← coerce? e ty | failure
  return e'

/--
Checks whether an expression is the coercion of some other expression,
and if so returns that expression.
-/
def isCoeOf? (e : Expr) : MetaM (Option Expr) := do
  if let Expr.const fn .. := e.getAppFn then
    if let some info ← getCoeFnInfo? fn then
      if e.getAppNumArgs == info.numArgs then
        return e.getArg! info.coercee
  return none

/--
Checks whether an expression is a numeral in some type,
and if so returns that type and the natural number.
-/
def isNumeral? (e : Expr) : Option (Expr × Nat) :=
  -- TODO: cleanup, and possibly remove duplicate
  if e.isConstOf ``Nat.zero then
    (mkConst ``Nat, 0)
  else if let Expr.app (Expr.app (Expr.app (Expr.const ``OfNat.ofNat ..) α ..)
      (Expr.lit (Literal.natVal n) ..) ..) .. := e then
    some (α, n)
  else
    none

/--
This is the main heuristic used alongside the elim and move lemmas.
The goal is to help casts move past operators by adding intermediate casts.
An expression of the shape:
```
op (↑(x : α) : γ) (↑(y : β) : γ)
```
is rewritten to:
```
op (↑(↑(x : α) : β) : γ) (↑(y : β) : γ)
```
when
```
(↑(↑(x : α) : β) : γ) = (↑(x : α) : γ)
```
can be proven with a squash lemma
-/
def splittingProcedure (expr : Expr) : MetaM Simp.Result := do
  let Expr.app (Expr.app op x ..) y .. := expr | return {expr}

  let Expr.forallE _ γ (Expr.forallE _ γ' ty ..) .. ← inferType op | return {expr}
  if γ'.hasLooseBVars || ty.hasLooseBVars then return {expr}
  unless ← isDefEq γ γ' do return {expr}

  let msg := m!"splitting {expr}"
  let msg
    | .error _ => return m!"{bombEmoji} {msg}"
    | .ok r => return if r.expr == expr then m!"{crossEmoji} {msg}" else
      m!"{checkEmoji} {msg} to {r.expr}"
  withTraceNode `Tactic.norm_cast msg do

  try
    let some x' ← isCoeOf? x | failure
    let some y' ← isCoeOf? y | failure
    let α ← inferType x'
    let β ← inferType y'

    -- TODO: fast timeout
    (try
      let x2 ← mkCoe (← mkCoe x' β) γ
      let some x_x2 ← proveEqUsingDown x x2 | failure
      Simp.mkCongrFun (← Simp.mkCongr {expr := op} x_x2) y
    catch _ =>
      let y2 ← mkCoe (← mkCoe y' α) γ
      let some y_y2 ← proveEqUsingDown y y2 | failure
      Simp.mkCongr {expr := mkApp op x} y_y2)
  catch _ => try
    let some (_, n) := isNumeral? y | failure
    let some x' ← isCoeOf? x | failure
    let α ← inferType x'
    let y2 ← mkCoe (← mkNumeral α n) γ
    let some y_y2 ← proveEqUsingDown y y2 | failure
    Simp.mkCongr {expr := mkApp op x} y_y2
  catch _ => try
    let some (_, n) := isNumeral? x | failure
    let some y' ← isCoeOf? y | failure
    let β ← inferType y'
    let x2 ← mkCoe (← mkNumeral β n) γ
    let some x_x2 ← proveEqUsingDown x x2 | failure
    Simp.mkCongrFun (← Simp.mkCongr {expr := op} x_x2) y
  catch _ =>
    return {expr}

/--
Discharging function used during simplification in the "squash" step.
-/
-- TODO: normCast takes a list of expressions to use as lemmas for the discharger
-- TODO: a tactic to print the results the discharger fails to prove
def prove (e : Expr) : SimpM (Option Expr) := do
  withTraceNode `Tactic.norm_cast (return m!"{exceptOptionEmoji ·} discharging: {e}") do
  return (← findLocalDeclWithType? e).map mkFVar

/--
Core rewriting function used in the "squash" step, which moves casts upwards
and eliminates them.

It tries to rewrite an expression using the elim and move lemmas.
On failure, it calls the splitting procedure heuristic.
-/
partial def upwardAndElim (up : SimpTheorems) (e : Expr) : SimpM Simp.Step := do
  -- Remark: we set `wellBehavedDischarge := false` because `prove` may access arbitrary elements in the local context.
  -- See comment at `Methods.wellBehavedDischarge`
  let r ← withDischarger prove (wellBehavedDischarge := false) do
    Simp.rewrite? e up.post up.erased (tag := "squash") (rflOnly := false)
  let r := r.getD { expr := e }
  let r ← r.mkEqTrans (← splittingProcedure r.expr)
  if r.expr == e then return Simp.Step.done {expr := e}
  return Simp.Step.visit r

/--
If possible, rewrites `(n : α)` to `(Nat.cast n : α)` where `n` is a numeral and `α ≠ ℕ`.
Returns a pair of the new expression and proof that they are equal.
-/
def numeralToCoe (e : Expr) : MetaM Simp.Result := do
  let some (α, n) := isNumeral? e | failure
  if (← whnf α).isConstOf ``Nat then failure
  let newE ← mkAppOptM ``Nat.cast #[α, none, toExpr n]
  let some pr ← proveEqUsingDown e newE | failure
  return pr

declare_config_elab elabNormCastConfig NormCastConfig

/--
The core simplification routine of `normCast`.
-/
def derive (e : Expr) (config : NormCastConfig := {}) : MetaM Simp.Result := do
  withTraceNode `Tactic.norm_cast (fun _ => return m!"{e}") do
  let e ← instantiateMVars e

  let config := config.toConfig
  let congrTheorems ← Meta.getSimpCongrTheorems

  let r : Simp.Result := { expr := e }

  let withTrace phase := withTraceNode `Tactic.norm_cast fun
    | .ok r => return m!"{r.expr} (after {phase})"
    | .error _ => return m!"{bombEmoji} {phase}"

  -- step 1: pre-processing of numerals
  let r ← withTrace "pre-processing numerals" do
    let post e := return Simp.Step.done (← try numeralToCoe e catch _ => pure {expr := e})
    let ctx ← Simp.mkContext config (congrTheorems := congrTheorems)
    r.mkEqTrans (← Simp.main r.expr ctx (methods := { post })).1

  -- step 2: casts are moved upwards and eliminated
  let r ← withTrace "moving upward, splitting and eliminating" do
    let post := upwardAndElim (← normCastExt.up.getTheorems)
    let ctx ← Simp.mkContext config (congrTheorems := congrTheorems)
    r.mkEqTrans (← Simp.main r.expr ctx (methods := { post })).1

  let simprocs ← ({} : Simp.SimprocsArray).add `reduceCtorEq false

  -- step 3: casts are squashed
  let r ← withTrace "squashing" do
    let simpTheorems := #[← normCastExt.squash.getTheorems]
    let ctx ← Simp.mkContext
      (config := config)
      (simpTheorems := simpTheorems)
      (congrTheorems := congrTheorems)
    r.mkEqTrans (← simp r.expr ctx simprocs).1

  return r

open Term
@[builtin_term_elab modCast] def elabModCast : TermElab := fun stx expectedType? => do
  match stx with
  | `(mod_cast $e:term) =>
    withExpectedType expectedType? fun expectedType => do
    if (← instantiateMVars expectedType).hasExprMVar then tryPostpone
    let expectedType' ← derive expectedType
    let e ← Term.elabTerm e expectedType'.expr
    synthesizeSyntheticMVars
    let eTy ← instantiateMVars (← inferType e)
    if eTy.hasExprMVar then tryPostpone
    let eTy' ← derive eTy
    unless ← isDefEq eTy'.expr expectedType'.expr do
      throwTypeMismatchError "mod_cast" expectedType'.expr eTy'.expr e
    let eTy_eq_expectedType ← eTy'.mkEqTrans (← expectedType'.mkEqSymm expectedType )
    eTy_eq_expectedType.mkCast e
  | _ => throwUnsupportedSyntax

/-- Implementation of the `norm_cast` tactic when operating on the main goal. -/
def normCastTarget (cfg : NormCastConfig) : TacticM Unit :=
  liftMetaTactic1 fun goal => do
    let tgt ← instantiateMVars (← goal.getType)
    let prf ← derive tgt cfg
    applySimpResultToTarget goal tgt prf

/-- Implementation of the `norm_cast` tactic when operating on a hypothesis. -/
def normCastHyp (cfg : NormCastConfig) (fvarId : FVarId) : TacticM Unit :=
  liftMetaTactic1 fun goal => do
    let hyp ← instantiateMVars (← fvarId.getDecl).type
    let prf ← derive hyp cfg
    return (← applySimpResultToLocalDecl goal fvarId prf false).map (·.snd)

@[builtin_tactic normCast0]
def evalNormCast0 : Tactic := fun stx => do
  match stx with
  | `(tactic| norm_cast0 $cfg $[$loc?]?) =>
    let loc := if let some loc := loc? then expandLocation loc else Location.targets #[] true
    let cfg ← elabNormCastConfig cfg
    withMainContext do
      match loc with
      | Location.targets hyps target =>
        if target then (normCastTarget cfg)
        (← getFVarIds hyps).forM (normCastHyp cfg)
      | Location.wildcard =>
        normCastTarget cfg
        (← (← getMainGoal).getNondepPropHyps).forM (normCastHyp cfg)
  | _ => throwUnsupportedSyntax

@[builtin_tactic Lean.Parser.Tactic.Conv.normCast]
def evalConvNormCast : Tactic :=
  open Elab.Tactic.Conv in fun _ => withMainContext do
    applySimpResult (← derive (← getLhs))

@[builtin_tactic pushCast]
def evalPushCast : Tactic := fun stx => do
  let { ctx, simprocs, dischargeWrapper } ← withMainContext do
    mkSimpContext (simpTheorems := pushCastExt.getTheorems) stx (eraseLocal := false)
  let ctx := ctx.setFailIfUnchanged false
  dischargeWrapper.with fun discharge? =>
    discard <| simpLocation ctx simprocs discharge? (expandOptLocation stx[5])

open Command in
@[builtin_command_elab Parser.Tactic.normCastAddElim] def elabAddElim : CommandElab := fun stx => do
  match stx with
  | `(norm_cast_add_elim $id:ident) =>
    Elab.Command.liftCoreM do MetaM.run' do
     addElim (← realizeGlobalConstNoOverload id)
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic.NormCast
