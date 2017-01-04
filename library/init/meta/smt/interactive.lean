/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.smt.smt_tactic init.meta.interactive

namespace smt_tactic
meta def skip : smt_tactic unit :=
return ()

meta def step {α : Type} (tac : smt_tactic α) : smt_tactic unit :=
tac >> return ()

namespace interactive
open interactive.types

meta def intros : smt_tactic unit :=
smt_tactic.intros

meta def close : smt_tactic unit :=
smt_tactic.close

meta def apply (q : qexpr0) : smt_tactic unit :=
tactic.interactive.apply q

meta def fapply (q : qexpr0) : smt_tactic unit :=
tactic.interactive.fapply q

meta def apply_instance : smt_tactic unit :=
tactic.apply_instance

meta def change (q : qexpr0) : smt_tactic unit :=
tactic.interactive.change q

meta def exact (q : qexpr0) : smt_tactic unit :=
tactic.interactive.exact q

meta def assert (h : ident) (c : colon_tk) (q : qexpr0) : smt_tactic unit :=
do e ← tactic.to_expr_strict q,
   smt_tactic.assert h e

meta def define (h : ident) (c : colon_tk) (q : qexpr0) : smt_tactic unit :=
do e ← tactic.to_expr_strict q,
   smt_tactic.define h e

meta def assertv (h : ident) (c : colon_tk) (q₁ : qexpr0) (a : assign_tk) (q₂ : qexpr0) : smt_tactic unit :=
do t ← tactic.to_expr_strict q₁,
   v ← tactic.to_expr_strict `((%%q₂ : %%t)),
   smt_tactic.assertv h t v

meta def definev (h : ident) (c : colon_tk) (q₁ : qexpr0) (a : assign_tk) (q₂ : qexpr0) : smt_tactic unit :=
do t ← tactic.to_expr_strict q₁,
   v ← tactic.to_expr_strict `((%%q₂ : %%t)),
   smt_tactic.definev h t v

meta def note (h : ident) (a : assign_tk) (q : qexpr0) : smt_tactic unit :=
do p ← tactic.to_expr_strict q,
   smt_tactic.note h p

meta def pose (h : ident) (a : assign_tk) (q : qexpr0) : smt_tactic unit :=
do p ← tactic.to_expr_strict q,
   smt_tactic.pose h p

meta def trace_state : smt_tactic unit :=
smt_tactic.trace_state

end interactive
end smt_tactic
