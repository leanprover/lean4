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
meta instance : has_to_string pexpr :=
⟨pexpr.to_string⟩

class has_to_pexpr (A : Type u) :=
(to_pexpr : A → pexpr)

meta definition to_pexpr {A : Type u} [has_to_pexpr A] : A → pexpr :=
has_to_pexpr.to_pexpr

meta instance : has_to_pexpr pexpr :=
⟨id⟩

meta instance : has_to_pexpr expr :=
⟨pexpr.of_expr⟩
