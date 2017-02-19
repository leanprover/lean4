/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.smt.smt_tactic init.meta.interactive
import init.meta.smt.rsimp

namespace smt_tactic
meta def save_info (p : pos) : smt_tactic unit :=
do (ss, ts) ← smt_tactic.read,
   tactic.save_info_thunk p (λ _, smt_state.to_format ss ts)

meta def skip : smt_tactic unit :=
return ()

meta def solve_goals : smt_tactic unit :=
repeat close

meta def step {α : Type} (tac : smt_tactic α) : smt_tactic unit :=
tac >> solve_goals

meta def istep {α : Type} (line : nat) (col : nat) (tac : smt_tactic α) : smt_tactic unit :=
λ ss ts, @scope_trace _ line col ((tac >> solve_goals) ss ts)

meta def rstep {α : Type} (line : nat) (col : nat) (tac : smt_tactic α) : smt_tactic unit :=
λ ss ts, result.cases_on (istep line col tac ss ts)
  (λ ⟨a, new_ss⟩ new_ts, result.success ((), new_ss) new_ts)
  (λ msg_thunk e, tactic.report_exception line col msg_thunk)

meta def execute (tac : smt_tactic unit) : tactic unit :=
using_smt tac

meta def execute_with (cfg : smt_config) (tac : smt_tactic unit) : tactic unit :=
using_smt tac cfg

namespace interactive
open lean.parser
open interactive
open interactive.types
local postfix ?:9001 := optional
local postfix *:9001 := many

meta def itactic : Type :=
smt_tactic unit

meta def irtactic : Type :=
smt_tactic unit

meta def intros : parse ident* → smt_tactic unit
| [] := smt_tactic.intros
| hs := smt_tactic.intro_lst hs

/--
  Try to close main goal by using equalities implied by the congruence
  closure module.
-/
meta def close : smt_tactic unit :=
smt_tactic.close

/--
  Produce new facts using heuristic lemma instantiation based on E-matching.
  This tactic tries to match patterns from lemmas in the main goal with terms
  in the main goal. The set of lemmas is populated with theorems
  tagged with the attribute specified at smt_config.em_attr, and lemmas
  added using tactics such as `smt_tactic.add_lemmas`.
  The current set of lemmas can be retrieved using the tactic `smt_tactic.get_lemmas`.
-/
meta def ematch : smt_tactic unit :=
smt_tactic.ematch

meta def apply (q : parse texpr) : smt_tactic unit :=
tactic.interactive.apply q

meta def fapply (q : parse texpr) : smt_tactic unit :=
tactic.interactive.fapply q

meta def apply_instance : smt_tactic unit :=
tactic.apply_instance

meta def change (q : parse texpr) : smt_tactic unit :=
tactic.interactive.change q

meta def exact (q : parse texpr) : smt_tactic unit :=
tactic.interactive.exact q

meta def assert (h : parse ident) (q : parse $ tk ":" *> texpr) : smt_tactic unit :=
do e ← tactic.to_expr_strict q,
   smt_tactic.assert h e

meta def define (h : parse ident) (q : parse $ tk ":" *> texpr) : smt_tactic unit :=
do e ← tactic.to_expr_strict q,
   smt_tactic.define h e

meta def assertv (h : parse ident) (q₁ : parse $ tk ":" *> texpr) (q₂ : parse $ tk ":=" *> texpr) : smt_tactic unit :=
do t ← tactic.to_expr_strict q₁,
   v ← tactic.to_expr_strict ``(%%q₂ : %%t),
   smt_tactic.assertv h t v

meta def definev (h : parse ident) (q₁ : parse $ tk ":" *> texpr) (q₂ : parse $ tk ":=" *> texpr) : smt_tactic unit :=
do t ← tactic.to_expr_strict q₁,
   v ← tactic.to_expr_strict ``(%%q₂ : %%t),
   smt_tactic.definev h t v

meta def note (h : parse ident) (q : parse $ tk ":=" *> texpr) : smt_tactic unit :=
do p ← tactic.to_expr_strict q,
   smt_tactic.note h p

meta def pose (h : parse ident) (q : parse $ tk ":=" *> texpr) : smt_tactic unit :=
do p ← tactic.to_expr_strict q,
   smt_tactic.pose h p

meta def add_fact (q : parse texpr) : smt_tactic unit :=
do h ← tactic.get_unused_name `h none,
   p ← tactic.to_expr_strict q,
   smt_tactic.note h p

meta def trace_state : smt_tactic unit :=
smt_tactic.trace_state

meta def trace {α : Type} [has_to_tactic_format α] (a : α) : smt_tactic unit :=
tactic.trace a

meta def destruct (q : parse texpr) : smt_tactic unit :=
do p ← tactic.to_expr_strict q,
   smt_tactic.destruct p

meta def by_cases (q : parse texpr) : smt_tactic unit :=
do p ← tactic.to_expr_strict q,
   smt_tactic.by_cases p

meta def by_contradiction : smt_tactic unit :=
smt_tactic.by_contradiction

meta def by_contra : smt_tactic unit :=
smt_tactic.by_contradiction

open tactic (resolve_name transparency to_expr)

private meta def report_invalid_em_lemma {α : Type} (n : name) : tactic α :=
fail ("invalid ematch lemma '" ++ to_string n ++ "'")

private meta def add_lemma_name (md : transparency) (lhs_lemma : bool) (n : name) (ref : expr) : smt_tactic unit :=
do
  e ← resolve_name n,
  match e with
  | expr.const n _           := (add_ematch_lemma_from_decl_core md lhs_lemma n >> tactic.save_const_type_info n ref) <|> report_invalid_em_lemma n
  | _                        := (add_ematch_lemma_core md lhs_lemma e >> try (tactic.save_type_info e ref)) <|> report_invalid_em_lemma n
  end


private meta def add_lemma_pexpr (md : transparency) (lhs_lemma : bool) (p : pexpr) : smt_tactic unit :=
let e := pexpr.to_raw_expr p in
match e with
| (expr.const c [])          := add_lemma_name md lhs_lemma c e
| (expr.local_const c _ _ _) := add_lemma_name md lhs_lemma c e
| _                          := do new_e ← to_expr p, add_ematch_lemma_core md lhs_lemma new_e
end

private meta def add_lemma_pexprs (md : transparency) (lhs_lemma : bool) : list pexpr → smt_tactic unit
| []      := return ()
| (p::ps) := add_lemma_pexpr md lhs_lemma p >> add_lemma_pexprs ps

meta def add_lemma (l : parse qexpr_list_or_texpr) : smt_tactic unit :=
add_lemma_pexprs reducible ff l

meta def add_lhs_lemma (l : parse qexpr_list_or_texpr) : smt_tactic unit :=
add_lemma_pexprs reducible tt l

private meta def add_eqn_lemmas_for_core (md : transparency) : list name → smt_tactic unit
| []      := return ()
| (c::cs) := do
  e ← resolve_name c,
  match e with
  | expr.const n _           := add_ematch_eqn_lemmas_for_core md n >> add_eqn_lemmas_for_core cs
  | _                        := fail $ "'" ++ to_string c ++ "' is not a constant"
  end

meta def add_eqn_lemmas_for (ids : parse ident*) : smt_tactic unit :=
add_eqn_lemmas_for_core reducible ids

meta def add_eqn_lemmas (ids : parse ident*) : smt_tactic unit :=
add_eqn_lemmas_for ids

private meta def add_hinst_lemma_from_name (md : transparency) (lhs_lemma : bool) (n : name) (hs : hinst_lemmas) (ref : expr) : smt_tactic hinst_lemmas :=
do
  e ← resolve_name n,
  match e with
  | expr.const n _           :=
    (do h ← hinst_lemma.mk_from_decl_core md n lhs_lemma, tactic.save_const_type_info n ref, return $ hs^.add h)
    <|>
    (do hs₁ ← mk_ematch_eqn_lemmas_for_core md n, tactic.save_const_type_info n ref, return $ hs^.merge hs₁)
    <|>
    report_invalid_em_lemma n
  | _ :=
    (do h ← hinst_lemma.mk_core md e lhs_lemma, try (tactic.save_type_info e ref), return $ hs^.add h)
    <|>
    report_invalid_em_lemma n
  end

private meta def add_hinst_lemma_from_pexpr (md : transparency) (lhs_lemma : bool) (p : pexpr) (hs : hinst_lemmas) : smt_tactic hinst_lemmas :=
let e := pexpr.to_raw_expr p in
match e with
| (expr.const c [])          := add_hinst_lemma_from_name md lhs_lemma c hs e
| (expr.local_const c _ _ _) := add_hinst_lemma_from_name md lhs_lemma c hs e
| _                          := do new_e ← to_expr p, h ← hinst_lemma.mk_core md new_e lhs_lemma, return $ hs^.add h
end

private meta def add_hinst_lemmas_from_pexprs (md : transparency) (lhs_lemma : bool) : list pexpr → hinst_lemmas → smt_tactic hinst_lemmas
| []      hs := return hs
| (p::ps) hs := do hs₁ ← add_hinst_lemma_from_pexpr md lhs_lemma p hs, add_hinst_lemmas_from_pexprs ps hs₁

meta def ematch_using (l : parse qexpr_list_or_texpr) : smt_tactic unit :=
do hs ← add_hinst_lemmas_from_pexprs reducible ff l hinst_lemmas.mk,
   smt_tactic.ematch_using hs

/-- Try the given tactic, and do nothing if it fails. -/
meta def try (t : itactic) : smt_tactic unit :=
smt_tactic.try t

/-- Keep applying the given tactic until it fails. -/
meta def repeat (t : itactic) : smt_tactic unit :=
smt_tactic.repeat t

/-- Apply the given tactic to all remaining goals. -/
meta def all_goals (t : itactic) : smt_tactic unit :=
smt_tactic.all_goals t

meta def induction (p : parse texpr) (rec_name : parse using_ident) (ids : parse with_ident_list) : smt_tactic unit :=
slift (tactic.interactive.induction p rec_name ids)

open tactic

/-- Simplify the target type of the main goal. -/
meta def simp (hs : parse opt_qexpr_list) (attr_names : parse with_ident_list) (ids : parse without_ident_list) (cfg : simp_config := {}) : smt_tactic unit :=
tactic.interactive.simp hs attr_names ids [] cfg

/-- Simplify the target type of the main goal using simplification lemmas and the current set of hypotheses. -/
meta def simp_using_hs (hs : parse opt_qexpr_list) (attr_names : parse with_ident_list) (ids : parse without_ident_list) (cfg : simp_config := {}) : smt_tactic unit :=
tactic.interactive.simp_using_hs hs attr_names ids cfg

meta def simph (hs : parse opt_qexpr_list) (attr_names : parse with_ident_list) (ids : parse without_ident_list) (cfg : simp_config := {}) : smt_tactic unit :=
simp_using_hs hs attr_names ids cfg

meta def dsimp (es : parse opt_qexpr_list) (attr_names : parse with_ident_list) (ids : parse without_ident_list) : smt_tactic unit :=
tactic.interactive.dsimp es attr_names ids []

meta def rsimp : smt_tactic unit :=
do ccs ← to_cc_state, rsimp.rsimplify_goal ccs

meta def add_simp_lemmas : smt_tactic unit :=
get_hinst_lemmas_for_attr `rsimp_attr >>= add_lemmas

/-- Keep applying heuristic instantiation until the current goal is solved, or it fails. -/
meta def eblast : smt_tactic unit :=
smt_tactic.eblast

/-- Keep applying heuristic instantiation using the given lemmas until the current goal is solved, or it fails. -/
meta def eblast_using (l : parse qexpr_list_or_texpr) : smt_tactic unit :=
do hs ← add_hinst_lemmas_from_pexprs reducible ff l hinst_lemmas.mk,
   smt_tactic.repeat (smt_tactic.ematch_using hs >> smt_tactic.try smt_tactic.close)

end interactive
end smt_tactic
