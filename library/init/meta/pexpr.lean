/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.expr
universe variables u

/- Quoted expressions. They can be converted into expressions by using a tactic. -/
meta constant pexpr : Type
protected meta constant pexpr.of_expr : expr → pexpr
protected meta constant pexpr.subst   : pexpr → pexpr → pexpr

meta constant pexpr.to_string : pexpr → string
attribute [instance]
meta definition pexpr.has_to_string : has_to_string pexpr :=
has_to_string.mk pexpr.to_string

structure [class] has_to_pexpr (A : Type u) :=
(to_pexpr : A → pexpr)

meta definition to_pexpr {A : Type u} [has_to_pexpr A] : A → pexpr :=
has_to_pexpr.to_pexpr

attribute [instance]
meta definition pexpr.has_to_pexpr : has_to_pexpr pexpr :=
has_to_pexpr.mk id

attribute [instance]
meta definition expr.has_to_pexpr : has_to_pexpr expr :=
has_to_pexpr.mk pexpr.of_expr
