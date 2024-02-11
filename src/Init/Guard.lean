/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
prelude
import Init.Tactics
import Init.Conv
import Init.NotationExtra

namespace Lean.Parser

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

namespace Tactic

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
@[inherit_doc guardExpr]
syntax (name := guardExprConv) "guard_expr " term:51 equal term : conv

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
@[inherit_doc guardTarget]
syntax (name := guardTargetConv) "guard_target " equal term : conv

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

end Tactic

namespace Command

/--
Command to check equality of two expressions.
* `#guard_expr e = e'` checks that `e` and `e'` are defeq at reducible transparency.
* `#guard_expr e =~ e'` checks that `e` and `e'` are defeq at default transparency.
* `#guard_expr e =ₛ e'` checks that `e` and `e'` are syntactically equal.
* `#guard_expr e =ₐ e'` checks that `e` and `e'` are alpha-equivalent.

This is a command version of the `guard_expr` tactic. -/
syntax (name := guardExprCmd) "#guard_expr " term:51 equal term : command

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
syntax (name := guardCmd) "#guard " term : command

end Command

end Lean.Parser
