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

meta def solve_goals : smt_tactic unit :=
repeat close

meta def step {α : Type} (tac : smt_tactic α) : smt_tactic unit :=
tac >> solve_goals

meta def execute (tac : smt_tactic unit) : tactic unit :=
using_smt tac

meta def execute_with (cfg : smt_config) (tac : smt_tactic unit) : tactic unit :=
using_smt_core cfg tac

namespace interactive
open interactive.types

meta def itactic : Type :=
smt_tactic unit

meta def intros : smt_tactic unit :=
smt_tactic.intros

meta def close : smt_tactic unit :=
smt_tactic.close

meta def ematch : smt_tactic unit :=
smt_tactic.ematch

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

meta def add_fact (q : qexpr0) : smt_tactic unit :=
do h ← tactic.get_unused_name `h none,
   p ← tactic.to_expr_strict q,
   smt_tactic.note h p

meta def trace_state : smt_tactic unit :=
smt_tactic.trace_state

meta def trace {α : Type} [has_to_tactic_format α] (a : α) : smt_tactic unit :=
tactic.trace a

meta def destruct (q : qexpr0) : smt_tactic unit :=
do p ← tactic.to_expr_strict q,
   smt_tactic.destruct p

meta def by_cases (q : qexpr0) : smt_tactic unit :=
do p ← tactic.to_expr_strict q,
   smt_tactic.by_cases p

meta def by_contradiction : smt_tactic unit :=
smt_tactic.by_contradiction

meta def by_contra : smt_tactic unit :=
smt_tactic.by_contradiction

open tactic (resolve_name transparency to_expr)

private meta def add_lemma_name (md : transparency) (lhs_lemma : bool) (n : name) : smt_tactic unit :=
do {
  e ← resolve_name n,
  match e with
  | expr.const n _           := add_ematch_lemma_from_decl_core md lhs_lemma n
  | expr.local_const _ _ _ _ := add_ematch_lemma_core md lhs_lemma e
  | _                        := failed
  end
}
<|>
fail ("invalid ematch lemma '" ++ to_string n ++ "'")

private meta def add_lemma_pexpr (md : transparency) (lhs_lemma : bool) (p : pexpr) : smt_tactic unit :=
let e := pexpr.to_raw_expr p in
match e with
| (expr.const c [])          := add_lemma_name md lhs_lemma c
| (expr.local_const c _ _ _) := add_lemma_name md lhs_lemma c
| _                          := do new_e ← to_expr p, add_ematch_lemma_core md lhs_lemma new_e
end

private meta def add_lemma_pexprs (md : transparency) (lhs_lemma : bool) : list pexpr → smt_tactic unit
| []      := return ()
| (p::ps) := add_lemma_pexpr md lhs_lemma p >> add_lemma_pexprs ps

meta def add_lemma (l : qexpr_list_or_qexpr0) : smt_tactic unit :=
add_lemma_pexprs reducible ff l

meta def add_lhs_lemma (l : qexpr_list_or_qexpr0) : smt_tactic unit :=
add_lemma_pexprs reducible tt l

private meta def add_eqn_lemmas_for_core (md : transparency) : list name → smt_tactic unit
| []      := return ()
| (c::cs) := do
  e ← resolve_name c,
  match e with
  | expr.const n _           := add_ematch_eqn_lemmas_for_core md n >> add_eqn_lemmas_for_core cs
  | _                        := fail $ "'" ++ to_string c ++ "' is not a constant"
  end

meta def add_eqn_lemmas_for (ids : raw_ident_list) : smt_tactic unit :=
add_eqn_lemmas_for_core reducible ids

meta def add_eqn_lemmas (ids : raw_ident_list) : smt_tactic unit :=
add_eqn_lemmas_for ids

private meta def add_hinst_lemma_from_name (md : transparency) (lhs_lemma : bool) (n : name) (hs : hinst_lemmas) : smt_tactic hinst_lemmas :=
do {
  e ← resolve_name n,
  match e with
  | expr.const n _           :=
    (do h ← hinst_lemma.mk_from_decl_core md n lhs_lemma, return $ hs^.add h)
    <|>
    (do hs₁ ← mk_ematch_eqn_lemmas_for_core md n, return $ hs^.merge hs₁)
  | expr.local_const _ _ _ _ := do h ← hinst_lemma.mk_core md e lhs_lemma, return $ hs^.add h
  | _                        := fail "failed"
  end
}
<|>
fail ("invalid ematch lemma '" ++ to_string n ++ "'")

private meta def add_hinst_lemma_from_pexpr (md : transparency) (lhs_lemma : bool) (p : pexpr) (hs : hinst_lemmas) : smt_tactic hinst_lemmas :=
let e := pexpr.to_raw_expr p in
match e with
| (expr.const c [])          := add_hinst_lemma_from_name md lhs_lemma c hs
| (expr.local_const c _ _ _) := add_hinst_lemma_from_name md lhs_lemma c hs
| _                          := do new_e ← to_expr p, h ← hinst_lemma.mk_core md new_e lhs_lemma, return $ hs^.add h
end

private meta def add_hinst_lemmas_from_pexprs (md : transparency) (lhs_lemma : bool) : list pexpr → hinst_lemmas → smt_tactic hinst_lemmas
| []      hs := return hs
| (p::ps) hs := do hs₁ ← add_hinst_lemma_from_pexpr md lhs_lemma p hs, add_hinst_lemmas_from_pexprs ps hs₁

meta def ematch_using (l : qexpr_list_or_qexpr0) : smt_tactic unit :=
do hs ← add_hinst_lemmas_from_pexprs reducible ff l hinst_lemmas.mk,
   smt_tactic.ematch_using hs

meta def try (t : itactic) : smt_tactic unit :=
smt_tactic.try t

meta def repeat (t : itactic) : smt_tactic unit :=
smt_tactic.repeat t

end interactive
end smt_tactic
