/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.expr
universe u

/- Quoted expressions. They can be converted into expressions by using a tactic. -/
@[reducible] meta def pexpr := expr ff
protected meta constant pexpr.of_expr  : expr → pexpr

meta constant pexpr.mk_placeholder : pexpr
meta constant pexpr.mk_field_macro : pexpr → name → pexpr
meta constant pexpr.mk_explicit : pexpr → pexpr

/- Choice macros are used to implement overloading. -/
meta constant pexpr.is_choice_macro : pexpr → bool

meta class has_to_pexpr (α : Type u) :=
(to_pexpr : α → pexpr)

meta def to_pexpr {α : Type u} [has_to_pexpr α] : α → pexpr :=
has_to_pexpr.to_pexpr

meta instance : has_to_pexpr pexpr :=
⟨id⟩

meta instance : has_to_pexpr expr :=
⟨pexpr.of_expr⟩
