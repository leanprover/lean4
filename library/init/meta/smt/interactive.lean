/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.smt.smt_tactic init.meta.interactive_base
import init.meta.smt.rsimp

namespace smt_tactic
meta def save_info (p : pos) : smt_tactic unit :=
do (ss, ts) ← smt_tactic.read,
   tactic.save_info_thunk p (λ _, smt_state.to_format ss ts)

meta def skip : smt_tactic unit :=
return ()

meta def solve_goals : smt_tactic unit :=
iterate close

meta def step {α : Type} (tac : smt_tactic α) : smt_tactic unit :=
tac >> solve_goals

meta def istep {α : Type} (line0 col0 line col : nat) (tac : smt_tactic α) : smt_tactic unit :=
⟨λ ss ts, (@scope_trace _ line col (λ _, (tac >> solve_goals).run ss ts)).clamp_pos line0 line col⟩

meta def execute (tac : smt_tactic unit) : tactic unit :=
using_smt tac

meta def execute_with (cfg : smt_config) (tac : smt_tactic unit) : tactic unit :=
using_smt tac cfg

namespace interactive
open lean.parser
open interactive
open interactive.types
local postfix `?`:9001 := optional
local postfix *:9001 := many

meta def itactic : Type :=
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
tactic.interactive.change q none (loc.ns [none])

meta def exact (q : parse texpr) : smt_tactic unit :=
tactic.interactive.exact q

meta def «from» := exact

meta def «assume» := tactic.interactive.assume

meta def «have» (h : parse ident?) (q₁ : parse (tk ":" *> texpr)?) (q₂ : parse $ (tk ":=" *> texpr)?) : smt_tactic unit :=
let h := h.get_or_else `this in
match q₁, q₂ with
| some e, some p := do
  t ← tactic.to_expr e,
  v ← tactic.to_expr ``(%%p : %%t),
  smt_tactic.assertv h t v
| none, some p := do
  p ← tactic.to_expr p,
  smt_tactic.note h none p
| some e, none := tactic.to_expr e >>= smt_tactic.assert h
| none, none := do
  u ← tactic.mk_meta_univ,
  e ← tactic.mk_meta_var (expr.sort u),
  smt_tactic.assert h e
end >> return ()

meta def «let» (h : parse ident?) (q₁ : parse (tk ":" *> texpr)?) (q₂ : parse $ (tk ":=" *> texpr)?) : smt_tactic unit :=
let h := h.get_or_else `this in
match q₁, q₂ with
| some e, some p := do
  t ← tactic.to_expr e,
  v ← tactic.to_expr ``(%%p : %%t),
  smt_tactic.definev h t v
| none, some p := do
  p ← tactic.to_expr p,
  smt_tactic.pose h none p
| some e, none := tactic.to_expr e >>= smt_tactic.define h
| none, none := do
  u ← tactic.mk_meta_univ,
  e ← tactic.mk_meta_var (expr.sort u),
  smt_tactic.define h e
end >> return ()

meta def add_fact (q : parse texpr) : smt_tactic unit :=
do h ← tactic.get_unused_name `h none,
   p ← tactic.to_expr_strict q,
   smt_tactic.note h none p

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

private meta def report_invalid_em_lemma {α : Type} (n : name) : smt_tactic α :=
fail format!"invalid ematch lemma '{n}'"

private meta def add_lemma_name (md : transparency) (lhs_lemma : bool) (n : name) (ref : pexpr) : smt_tactic unit :=
do
  p ← resolve_name n,
  match p with
  | expr.const n _           := (add_ematch_lemma_from_decl_core md lhs_lemma n >> tactic.save_const_type_info n ref) <|> report_invalid_em_lemma n
  | _                        := (do e ← to_expr p, add_ematch_lemma_core md lhs_lemma e >> try (tactic.save_type_info e ref)) <|> report_invalid_em_lemma n
  end


private meta def add_lemma_pexpr (md : transparency) (lhs_lemma : bool) (p : pexpr) : smt_tactic unit :=
match p with
| (expr.const c [])          := add_lemma_name md lhs_lemma c p
| (expr.local_const c _ _ _) := add_lemma_name md lhs_lemma c p
| _                          := do new_e ← to_expr p, add_ematch_lemma_core md lhs_lemma new_e
end

private meta def add_lemma_pexprs (md : transparency) (lhs_lemma : bool) : list pexpr → smt_tactic unit
| []      := return ()
| (p::ps) := add_lemma_pexpr md lhs_lemma p >> add_lemma_pexprs ps

meta def add_lemma (l : parse pexpr_list_or_texpr) : smt_tactic unit :=
add_lemma_pexprs reducible ff l

meta def add_lhs_lemma (l : parse pexpr_list_or_texpr) : smt_tactic unit :=
add_lemma_pexprs reducible tt l

private meta def add_eqn_lemmas_for_core (md : transparency) : list name → smt_tactic unit
| []      := return ()
| (c::cs) := do
  p ← resolve_name c,
  match p with
  | expr.const n _           := add_ematch_eqn_lemmas_for_core md n >> add_eqn_lemmas_for_core cs
  | _                        := fail format!"'{c}' is not a constant"
  end

meta def add_eqn_lemmas_for (ids : parse ident*) : smt_tactic unit :=
add_eqn_lemmas_for_core reducible ids

meta def add_eqn_lemmas (ids : parse ident*) : smt_tactic unit :=
add_eqn_lemmas_for ids

private meta def add_hinst_lemma_from_name (md : transparency) (lhs_lemma : bool) (n : name) (hs : hinst_lemmas) (ref : pexpr) : smt_tactic hinst_lemmas :=
do
  p ← resolve_name n,
  match p with
  | expr.const n _           :=
    (do h ← hinst_lemma.mk_from_decl_core md n lhs_lemma, tactic.save_const_type_info n ref, return $ hs.add h)
    <|>
    (do hs₁ ← mk_ematch_eqn_lemmas_for_core md n, tactic.save_const_type_info n ref, return $ hs.merge hs₁)
    <|>
    report_invalid_em_lemma n
  | _ :=
    (do e ← to_expr p, h ← hinst_lemma.mk_core md e lhs_lemma, try (tactic.save_type_info e ref), return $ hs.add h)
    <|>
    report_invalid_em_lemma n
  end

private meta def add_hinst_lemma_from_pexpr (md : transparency) (lhs_lemma : bool) (p : pexpr) (hs : hinst_lemmas) : smt_tactic hinst_lemmas :=
match p with
| (expr.const c [])          := add_hinst_lemma_from_name md lhs_lemma c hs p
| (expr.local_const c _ _ _) := add_hinst_lemma_from_name md lhs_lemma c hs p
| _                          := do new_e ← to_expr p, h ← hinst_lemma.mk_core md new_e lhs_lemma, return $ hs.add h
end

private meta def add_hinst_lemmas_from_pexprs (md : transparency) (lhs_lemma : bool) : list pexpr → hinst_lemmas → smt_tactic hinst_lemmas
| []      hs := return hs
| (p::ps) hs := do hs₁ ← add_hinst_lemma_from_pexpr md lhs_lemma p hs, add_hinst_lemmas_from_pexprs ps hs₁

meta def ematch_using (l : parse pexpr_list_or_texpr) : smt_tactic unit :=
do hs ← add_hinst_lemmas_from_pexprs reducible ff l hinst_lemmas.mk,
   smt_tactic.ematch_using hs

/-- Try the given tactic, and do nothing if it fails. -/
meta def try (t : itactic) : smt_tactic unit :=
smt_tactic.try t

/-- Keep applying the given tactic until it fails. -/
meta def iterate (t : itactic) : smt_tactic unit :=
smt_tactic.iterate t

/-- Apply the given tactic to all remaining goals. -/
meta def all_goals (t : itactic) : smt_tactic unit :=
smt_tactic.all_goals t

meta def induction (p : parse tactic.interactive.cases_arg_p) (rec_name : parse using_ident) (ids : parse with_ident_list)
  (revert : parse $ (tk "generalizing" *> ident*)?) : smt_tactic unit :=
slift (tactic.interactive.induction p rec_name ids revert)

open tactic

/-- Simplify the target type of the main goal. -/
meta def simp (use_iota_eqn : parse $ (tk "!")?) (no_dflt : parse only_flag) (hs : parse simp_arg_list)
              (attr_names : parse with_ident_list) (cfg : simp_config_ext := {}) : smt_tactic unit :=
tactic.interactive.simp use_iota_eqn no_dflt hs attr_names (loc.ns [none]) cfg

meta def dsimp (no_dflt : parse only_flag) (es : parse simp_arg_list) (attr_names : parse with_ident_list) : smt_tactic unit :=
tactic.interactive.dsimp no_dflt es attr_names (loc.ns [none])

meta def rsimp : smt_tactic unit :=
do ccs ← to_cc_state, _root_.rsimp.rsimplify_goal ccs

meta def add_simp_lemmas : smt_tactic unit :=
get_hinst_lemmas_for_attr `rsimp_attr >>= add_lemmas

/-- Keep applying heuristic instantiation until the current goal is solved, or it fails. -/
meta def eblast : smt_tactic unit :=
smt_tactic.eblast

/-- Keep applying heuristic instantiation using the given lemmas until the current goal is solved, or it fails. -/
meta def eblast_using (l : parse pexpr_list_or_texpr) : smt_tactic unit :=
do hs ← add_hinst_lemmas_from_pexprs reducible ff l hinst_lemmas.mk,
   smt_tactic.iterate (smt_tactic.ematch_using hs >> smt_tactic.try smt_tactic.close)

meta def guard_expr_eq (t : expr) (p : parse $ tk ":=" *> texpr) : smt_tactic unit :=
do e ← to_expr p, guard (expr.alpha_eqv t e)

meta def guard_target (p : parse texpr) : smt_tactic unit :=
do t ← target, guard_expr_eq t p

end interactive
end smt_tactic
