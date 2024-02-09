/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Elab.Command
import Lean.Elab.Tactic.Conv.Basic
import Lean.Meta.Basic
import Lean.Meta.Eval

namespace Lean.Elab.Tactic.GuardExpr
open Lean Meta Elab Tactic

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

/-- Reducible defeq matching for `guard_hyp` types -/
syntax colonR := " : "
/-- Default-reducibility defeq matching for `guard_hyp` types -/
syntax colonD := " :~ "
/-- Syntactic matching for `guard_hyp` types -/
syntax colonS := " :ₛ "
/-- Alpha-eq matching for `guard_hyp` types -/
syntax colonA := " :ₐ "
/-- The `guard_hyp` type specifier, one of `:`, `:~`, `:ₛ`, `:ₐ` -/
syntax colon := colonR <|> colonD <|> colonS <|> colonA

/-- Reducible defeq matching for `guard_hyp` values -/
syntax colonEqR := " := "
/-- Default-reducibility defeq matching for `guard_hyp` values -/
syntax colonEqD := " :=~ "
/-- Syntactic matching for `guard_hyp` values -/
syntax colonEqS := " :=ₛ "
/-- Alpha-eq matching for `guard_hyp` values -/
syntax colonEqA := " :=ₐ "
/-- The `guard_hyp` value specifier, one of `:=`, `:=~`, `:=ₛ`, `:=ₐ` -/
syntax colonEq := colonEqR <|> colonEqD <|> colonEqS <|> colonEqA

/-- Reducible defeq matching for `guard_expr` -/
syntax equalR := " = "
/-- Default-reducibility defeq matching for `guard_expr` -/
syntax equalD := " =~ "
/-- Syntactic matching for `guard_expr` -/
syntax equalS := " =ₛ "
/-- Alpha-eq matching for `guard_expr` -/
syntax equalA := " =ₐ "
/-- The `guard_expr` matching specifier, one of `=`, `=~`, `=ₛ`, `=ₐ` -/
syntax equal := equalR <|> equalD <|> equalS <|> equalA

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

/--
Tactic to check equality of two expressions.
* `guard_expr e = e'` checks that `e` and `e'` are defeq at reducible transparency.
* `guard_expr e =~ e'` checks that `e` and `e'` are defeq at default transparency.
* `guard_expr e =ₛ e'` checks that `e` and `e'` are syntactically equal.
* `guard_expr e =ₐ e'` checks that `e` and `e'` are alpha-equivalent.

Both `e` and `e'` are elaborated then have their metavariables instantiated before the equality
check. Their types are unified (using `isDefEqGuarded`) before synthetic metavariables are
processed, which helps with default instance handling.
-/
syntax (name := guardExpr) "guard_expr " term:51 equal term : tactic
@[inherit_doc guardExpr] syntax (name := guardExprConv) "guard_expr " term:51 equal term : conv

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

@[inherit_doc guardExpr, tactic guardExpr, tactic guardExprConv]
def evalGuardExpr : Tactic := fun
  | `(tactic| guard_expr $r $eq:equal $p)
  | `(conv| guard_expr $r $eq:equal $p) => withMainContext do
    let some mk := equal.toMatchKind eq | throwUnsupportedSyntax
    let res ← elabAndEvalMatchKind mk r p
    -- Note: `{eq}` itself prints a space before the relation.
    unless res do throwError "failed: {r}{eq} {p} is not true"
  | _ => throwUnsupportedSyntax

/--
Tactic to check that the target agrees with a given expression.
* `guard_target = e` checks that the target is defeq at reducible transparency to `e`.
* `guard_target =~ e` checks that the target is defeq at default transparency to `e`.
* `guard_target =ₛ e` checks that the target is syntactically equal to `e`.
* `guard_target =ₐ e` checks that the target is alpha-equivalent to `e`.

The term `e` is elaborated with the type of the goal as the expected type, which is mostly
useful within `conv` mode.
-/
syntax (name := guardTarget) "guard_target " equal term : tactic
@[inherit_doc guardTarget] syntax (name := guardTargetConv) "guard_target " equal term : conv

@[inherit_doc guardTarget, tactic guardTarget, tactic guardTargetConv]
def evalGuardTarget : Tactic :=
  let go eq r getTgt := withMainContext do
    let t ← getTgt >>= instantiateMVars
    let r ← elabTerm r (← inferType t)
    let some mk := equal.toMatchKind eq | throwUnsupportedSyntax
    unless ← mk.isEq r t do
      throwError "target of main goal is{indentExpr t}\nnot{indentExpr r}"
  fun
  | `(tactic| guard_target $eq $r) => go eq r getMainTarget
  | `(conv| guard_target $eq $r) => go eq r Conv.getLhs
  | _ => throwUnsupportedSyntax

/--
Tactic to check that a named hypothesis has a given type and/or value.

* `guard_hyp h : t` checks the type up to reducible defeq,
* `guard_hyp h :~ t` checks the type up to default defeq,
* `guard_hyp h :ₛ t` checks the type up to syntactic equality,
* `guard_hyp h :ₐ t` checks the type up to alpha equality.
* `guard_hyp h := v` checks value up to reducible defeq,
* `guard_hyp h :=~ v` checks value up to default defeq,
* `guard_hyp h :=ₛ v` checks value up to syntactic equality,
* `guard_hyp h :=ₐ v` checks the value up to alpha equality.

The value `v` is elaborated using the type of `h` as the expected type.
-/
syntax (name := guardHyp)
  "guard_hyp " term:max (colon term)? (colonEq term)? : tactic
@[inherit_doc guardHyp] syntax (name := guardHypConv)
  "guard_hyp " term:max (colon term)? (colonEq term)? : conv

@[inherit_doc guardHyp, tactic guardHyp, tactic guardHypConv]
def evalGuardHyp : Tactic := fun
  | `(tactic| guard_hyp $h $[$c $ty]? $[$eq $val]?)
  | `(conv| guard_hyp $h $[$c $ty]? $[$eq $val]?) => withMainContext do
    let fvarid ← getFVarId h
    let lDecl ←
      match (← getLCtx).find? fvarid with
      | none => throwError m!"hypothesis {h} not found"
      | some lDecl => pure lDecl
    if let (some c, some p) := (c, ty) then
      let some mk := colon.toMatchKind c | throwUnsupportedSyntax
      let e ← elabTerm p none
      let hty ← instantiateMVars lDecl.type
      unless ← mk.isEq e hty do
        throwError m!"hypothesis {h} has type{indentExpr hty}\nnot{indentExpr e}"
    match lDecl.value?, val with
    | none, some _        => throwError m!"{h} is not a let binding"
    | some _, none        => throwError m!"{h} is a let binding"
    | some hval, some val =>
      let some mk := eq.bind colonEq.toMatchKind | throwUnsupportedSyntax
      let e ← elabTerm val lDecl.type
      let hval ← instantiateMVars hval
      unless ← mk.isEq e hval do
        throwError m!"hypothesis {h} has value{indentExpr hval}\nnot{indentExpr e}"
    | none, none          => pure ()
  | _ => throwUnsupportedSyntax

/--
Command to check equality of two expressions.
* `#guard_expr e = e'` checks that `e` and `e'` are defeq at reducible transparency.
* `#guard_expr e =~ e'` checks that `e` and `e'` are defeq at default transparency.
* `#guard_expr e =ₛ e'` checks that `e` and `e'` are syntactically equal.
* `#guard_expr e =ₐ e'` checks that `e` and `e'` are alpha-equivalent.

This is a command version of the `guard_expr` tactic. -/
syntax (name := guardExprCmd) "#guard_expr " term:51 equal term : command

@[inherit_doc guardExprCmd, command_elab guardExprCmd]
def evalGuardExprCmd : Lean.Elab.Command.CommandElab
  | `(command| #guard_expr $r $eq:equal $p) =>
    Lean.Elab.Command.runTermElabM fun _ => do
      let some mk := equal.toMatchKind eq | throwUnsupportedSyntax
      let res ← elabAndEvalMatchKind mk r p
      -- Note: `{eq}` itself prints a space before the relation.
      unless res do throwError "failed: {r}{eq} {p} is not true"
  | _ => throwUnsupportedSyntax

/--
Command to check that an expression evaluates to `true`.

`#guard e` elaborates `e` ensuring its type is `Bool` then evaluates `e` and checks that
the result is `true`. The term is elaborated *without* variables declared using `variable`, since
these cannot be evaluated.

Since this makes use of coercions, so long as a proposition `p` is decidable, one can write
`#guard p` rather than `#guard decide p`. A consequence to this is that if there is decidable
equality one can write `#guard a = b`. Note that this is not exactly the same as checking
if `a` and `b` evaluate to the same thing since it uses the `DecidableEq` instance to do
the evaluation.

Note: this uses the untrusted evaluator, so `#guard` passing is *not* a proof that the
expression equals `true`. -/
elab "#guard " e:term : command =>
  Lean.Elab.Command.liftTermElabM do
    let e ← Term.elabTermEnsuringType e (mkConst ``Bool)
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let mvars ← getMVars e
    if mvars.isEmpty then
      let v ← unsafe evalExpr Bool (mkConst ``Bool) e
      unless v do
        throwError "expression{indentExpr e}\ndid not evaluate to `true`"
    else
      _ ← Term.logUnassignedUsingErrorInfos mvars
