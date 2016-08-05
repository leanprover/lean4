/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.expr

/- Quoted expressions. They can be converted into expressions by using a tactic. -/
meta_constant pexpr : Type₁
protected meta_constant pexpr.of_expr : expr → pexpr
protected meta_constant pexpr.subst   : pexpr → pexpr → pexpr

meta_constant pexpr.to_string : pexpr → string
meta_definition pexpr.has_to_string [instance] : has_to_string pexpr :=
has_to_string.mk pexpr.to_string

structure has_to_pexpr [class] (A : Type) :=
(to_pexpr : A → pexpr)

meta_definition to_pexpr {A : Type} [has_to_pexpr A] : A → pexpr :=
has_to_pexpr.to_pexpr

meta_definition pexpr.has_to_pexpr [instance] : has_to_pexpr pexpr :=
has_to_pexpr.mk id

meta_definition expr.has_to_pexpr [instance] : has_to_pexpr expr :=
has_to_pexpr.mk pexpr.of_expr
