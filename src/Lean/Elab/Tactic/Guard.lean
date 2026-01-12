/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Leonardo de Moura
-/
module

prelude
public import Init.Guard
public import Lean.Elab.Command
public import Lean.Elab.Tactic.Conv.Basic

public section

namespace Lean.Elab.Tactic.GuardExpr
open Meta

/--
The various `guard_*` tactics have similar matching specifiers for how equal expressions
have to be to pass the tactic.
This inductive gives the different specifiers that can be selected.
-/
inductive MatchKind
/-- A syntactic match means that the `Expr`s are `==` after stripping `MData` -/
| syntactic
/-- A defeq match `isDefEqGuarded` returns true. (Note that unification is allowed here.) -/
| defEq (red : TransparencyMode := .reducible)
/-- An alpha-eq match means that `Expr.eqv` returns true. -/
| alphaEq

open Lean.Parser Lean.Parser.Tactic Lean.Parser.Command

/-- Converts a `colon` syntax into a `MatchKind` -/
def colon.toMatchKind : TSyntax ``colon → Option MatchKind
  | `(colon| :) => some .defEq
  | `(colon| :~) => some (.defEq .default)
  | `(colon| :ₛ) => some .syntactic
  | `(colon| :ₐ) => some .alphaEq
  | _ => none

/-- Converts a `colonEq` syntax into a `MatchKind` -/
def colonEq.toMatchKind : TSyntax ``colonEq → Option MatchKind
  | `(colonEq| :=) => some .defEq
  | `(colonEq| :=~) => some (.defEq .default)
  | `(colonEq| :=ₛ) => some .syntactic
  | `(colonEq| :=ₐ) => some .alphaEq
  | _ => none

/-- Converts a `equal` syntax into a `MatchKind` -/
def equal.toMatchKind : TSyntax ``equal → Option MatchKind
  | `(equal| =) => some .defEq
  | `(equal| =~) => some (.defEq .default)
  | `(equal| =ₛ) => some .syntactic
  | `(equal| =ₐ) => some .alphaEq
  | _ => none

/-- Applies the selected matching rule to two expressions. -/
def MatchKind.isEq (a b : Expr) : MatchKind → MetaM Bool
  | .syntactic => return a.consumeMData == b.consumeMData
  | .alphaEq => return a.eqv b
  | .defEq red => withoutModifyingState <| withTransparency red <| Lean.Meta.isDefEqGuarded a b

/-- Produces a string description of the relation expressed by the given match kind. -/
def MatchKind.toStringDescr : MatchKind → String
  | .syntactic => "syntactically equal to"
  | .defEq .default => s!"definitionally equal to"
  | .defEq .all => s!"definitionally equal (unfolding all constants) to"
  | .defEq .reducible => s!"definitionally equal (unfolding reducible constants) to"
  | .defEq .instances => s!"definitionally equal (unfolding instances) to"
  | .defEq .none => s!"definitionally equal (not unfolding any constants) to"
  | .alphaEq => "alpha-equivalent to"

/-- Elaborate `a` and `b` and then do the given equality test `mk`. We make sure to unify
the types of `a` and `b` after elaboration so that when synthesizing pending metavariables
we don't get the wrong instances due to default instances (for example, for nat literals). -/
def elabAndEvalMatchKind (mk : MatchKind) (a b : Term) : TermElabM Bool :=
  Term.withoutErrToSorry do
    let a ← Term.elabTerm a none
    let b ← Term.elabTerm b none
    -- Unify types before synthesizing pending metavariables:
    _ ← isDefEqGuarded (← inferType a) (← inferType b)
    Term.synthesizeSyntheticMVarsNoPostponing
    mk.isEq (← instantiateMVars a) (← instantiateMVars b)

@[builtin_tactic guardExpr]
def evalGuardExpr : Tactic := fun
  | `(tactic| guard_expr $r $eq:equal $p)
  | `(conv| guard_expr $r $eq:equal $p) => withMainContext do
    let some mk := equal.toMatchKind eq | throwUnsupportedSyntax
    let res ← elabAndEvalMatchKind mk r p
    unless res do throwError "Failed: `{r}` is not {mk.toStringDescr} `{p}`"
  | _ => throwUnsupportedSyntax

-- TODO: This is workaround. We currently allow two occurrences of `builtin_tactic`.
@[builtin_tactic guardExprConv]
def evalGuardExprConv : Tactic := evalGuardExpr

@[builtin_tactic guardTarget]
def evalGuardTarget : Tactic :=
  let go eq r getTgt := withMainContext do
    let t ← getTgt >>= instantiateMVars
    let r ← elabTerm r (← inferType t)
    let some mk := equal.toMatchKind eq | throwUnsupportedSyntax
    unless ← mk.isEq r t do
      throwError "The main goal is{indentExpr t}\nbut was expected to be{indentExpr r}"
  fun
  | `(tactic| guard_target $eq $r) => go eq r getMainTarget
  | `(conv| guard_target $eq $r) => go eq r Conv.getLhs
  | _ => throwUnsupportedSyntax

-- See comment above
@[builtin_tactic guardTargetConv]
def evalGuardTargetConv : Tactic := evalGuardTarget

@[builtin_tactic guardHyp]
def evalGuardHyp : Tactic := fun
  | `(tactic| guard_hyp $h $[$c $ty]? $[$eq $val]?)
  | `(conv| guard_hyp $h $[$c $ty]? $[$eq $val]?) => withMainContext do
    let fvarid ← getFVarId h
    let lDecl ←
      match (← getLCtx).find? fvarid with
      | none => throwError m!"Hypothesis `{h}` not found"
      | some lDecl => pure lDecl
    if let (some c, some p) := (c, ty) then
      let some mk := colon.toMatchKind c | throwUnsupportedSyntax
      let e ← elabTerm p none
      let hty ← instantiateMVars lDecl.type
      unless ← mk.isEq e hty do
        throwError m!"Hypothesis `{h}` has type{indentExpr hty}\nbut was expected to have type{indentExpr e}"
    match lDecl.value?, val with
    | none, some _        => throwError m!"`{h}` is not a let binding"
    | some _, none        => throwError m!"`{h}` is a let binding"
    | some hval, some val =>
      let some mk := eq.bind colonEq.toMatchKind | throwUnsupportedSyntax
      let e ← elabTerm val lDecl.type
      let hval ← instantiateMVars hval
      unless ← mk.isEq e hval do
        throwError m!"Hypothesis `{h}` has value{indentExpr hval}\nbut was expected to have value{indentExpr e}"
    | none, none          => pure ()
  | _ => throwUnsupportedSyntax

@[builtin_tactic guardHypConv]
def evalGuardHypConv : Tactic := evalGuardHyp

@[builtin_command_elab guardExprCmd]
def evalGuardExprCmd : Lean.Elab.Command.CommandElab
  | `(command| #guard_expr $r $eq:equal $p) =>
    Lean.Elab.Command.runTermElabM fun _ => do
      let some mk := equal.toMatchKind eq | throwUnsupportedSyntax
      let res ← elabAndEvalMatchKind mk r p
      unless res do throwError "Failed: `{r}` is not {mk.toStringDescr} `{p}`"
  | _ => throwUnsupportedSyntax

@[builtin_command_elab guardCmd]
def evalGuardCmd : Lean.Elab.Command.CommandElab
  | `(command| #guard $e:term) => Lean.Elab.Command.liftTermElabM do
    let e ← Term.elabTermEnsuringType e (mkConst ``Bool)
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let mvars ← getMVars e
    if mvars.isEmpty then
      let v ← unsafe evalExpr (checkMeta := false) Bool (mkConst ``Bool) e
      unless v do
        throwError "Expression{indentExpr e}\ndid not evaluate to `true`"
    else
      _ ← Term.logUnassignedUsingErrorInfos mvars
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic.GuardExpr
