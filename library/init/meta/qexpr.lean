/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.expr

/- Quoted expressions. They can be converted into expressions by using a tactic. -/
meta_constant qexpr : Type₁
protected meta_constant qexpr.of_expr : expr → qexpr
protected meta_constant qexpr.subst   : qexpr → qexpr → qexpr

meta_constant qexpr.to_string : qexpr → string
meta_definition qexpr.has_to_string [instance] : has_to_string qexpr :=
has_to_string.mk qexpr.to_string

structure has_to_qexpr [class] (A : Type) :=
(to_qexpr : A → qexpr)

meta_definition to_qexpr {A : Type} [has_to_qexpr A] : A → qexpr :=
has_to_qexpr.to_qexpr

meta_definition qexpr.has_to_qexpr [instance] : has_to_qexpr qexpr :=
has_to_qexpr.mk id

meta_definition expr.has_to_qexpr [instance] : has_to_qexpr expr :=
has_to_qexpr.mk qexpr.of_expr
