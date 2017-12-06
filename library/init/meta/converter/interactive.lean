/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Converter monad for building simplifiers.
-/
prelude
import init.meta.interactive init.meta.converter.conv

namespace conv
meta def save_info (p : pos) : conv unit :=
do s ← tactic.read,
   tactic.save_info_thunk p (λ _, s.to_format tt)

meta def step {α : Type} (c : conv α) : conv unit :=
c >> return ()

meta def istep {α : Type} (line0 col0 line col : nat) (c : conv α) : conv unit :=
tactic.istep line0 col0 line col c

meta def execute (c : conv unit) : tactic unit :=
c

meta def solve1 (c : conv unit) : conv unit :=
tactic.solve1 $ c >> tactic.try (tactic.any_goals tactic.reflexivity)

namespace interactive
open lean
open lean.parser
open interactive
open interactive.types

meta def itactic : Type :=
conv unit

meta def skip : conv unit :=
conv.skip

meta def whnf : conv unit :=
conv.whnf

meta def dsimp (no_dflt : parse only_flag) (es : parse tactic.simp_arg_list) (attr_names : parse with_ident_list)
               (cfg : tactic.dsimp_config := {}) : conv unit :=
do (s, u) ← tactic.mk_simp_set no_dflt attr_names es,
   conv.dsimp (some s) u cfg

meta def trace_lhs : conv unit :=
lhs >>= tactic.trace

meta def change (p : parse texpr) : conv unit :=
tactic.i_to_expr p >>= conv.change

meta def congr : conv unit :=
conv.congr

meta def funext : conv unit :=
conv.funext

private meta def is_relation : conv unit :=
(lhs >>= tactic.relation_lhs_rhs >> return ())
<|>
tactic.fail "current expression is not a relation"

meta def to_lhs : conv unit :=
is_relation >> congr >> tactic.swap >> skip

meta def to_rhs : conv unit :=
is_relation >> congr >> skip

meta def done : conv unit :=
tactic.done

meta def find (p : parse parser.pexpr) (c : itactic) : conv unit :=
do (r, lhs, _) ← tactic.target_lhs_rhs,
   pat ← tactic.pexpr_to_pattern p,
   s   ← simp_lemmas.mk_default, -- to be able to use congruence lemmas @[congr]
   (found, new_lhs, pr) ←
     tactic.ext_simplify_core ff {zeta := ff, beta := ff, single_pass := tt, eta := ff,
                                  proj := ff, fail_if_unchanged := ff, memoize := ff} s
       (λ u, return u)
       (λ found s r p e, do
         guard (not found),
         matched ← (tactic.match_pattern pat e >> return tt) <|> return ff,
         guard matched,
         ⟨new_e, pr⟩ ← c.convert e r,
         return (tt, new_e, pr, ff))
       (λ a s r p e, tactic.failed)
       r lhs,
  when (not found) $ tactic.fail "find converter failed, pattern was not found",
  update_lhs new_lhs pr

meta def for (p : parse parser.pexpr) (occs : parse (list_of small_nat)) (c : itactic) : conv unit :=
do (r, lhs, _) ← tactic.target_lhs_rhs,
   pat ← tactic.pexpr_to_pattern p,
   s   ← simp_lemmas.mk_default, -- to be able to use congruence lemmas @[congr]
   (found, new_lhs, pr) ←
     tactic.ext_simplify_core 1 {zeta := ff, beta := ff, single_pass := tt, eta := ff,
                                 proj := ff, fail_if_unchanged := ff, memoize := ff} s
       (λ u, return u)
       (λ i s r p e, do
         matched ← (tactic.match_pattern pat e >> return tt) <|> return ff,
         guard matched,
         if i ∈ occs then do
           ⟨new_e, pr⟩ ← c.convert e r,
           return (i+1, new_e, some pr, tt)
         else return (i+1, e, none, tt))
       (λ a s r p e, tactic.failed)
       r lhs,
  update_lhs new_lhs pr

meta def simp (no_dflt : parse only_flag) (hs : parse tactic.simp_arg_list) (attr_names : parse with_ident_list)
              (cfg : tactic.simp_config_ext := {})
              : conv unit :=
do (s, u) ← tactic.mk_simp_set no_dflt attr_names hs,
   (r, lhs, rhs) ← tactic.target_lhs_rhs,
   (new_lhs, pr) ← tactic.simplify s u lhs cfg.to_simp_config r cfg.discharger,
   update_lhs new_lhs pr,
   return ()

meta def guard_lhs (p : parse texpr) : tactic unit :=
do t ← lhs, tactic.interactive.guard_expr_eq t p

section rw
open tactic.interactive (rw_rules rw_rule get_rule_eqn_lemmas to_expr')
open tactic (rewrite_cfg)

private meta def rw_lhs (h : expr) (cfg : rewrite_cfg) : conv unit :=
do l ← conv.lhs,
   (new_lhs, prf, _) ← tactic.rewrite h l cfg,
   update_lhs new_lhs prf

private meta def rw_core (rs : list rw_rule) (cfg : rewrite_cfg) : conv unit :=
rs.mmap' $ λ r, do
 save_info r.pos,
 eq_lemmas ← get_rule_eqn_lemmas r,
 orelse'
   (do h ← to_expr' r.rule, rw_lhs h {symm := r.symm, ..cfg})
   (eq_lemmas.mfirst $ λ n, do e ← tactic.mk_const n, rw_lhs e {symm := r.symm, ..cfg})
   (eq_lemmas.empty)

meta def rewrite (q : parse rw_rules) (cfg : rewrite_cfg := {}) : conv unit :=
rw_core q.rules cfg

meta def rw (q : parse rw_rules) (cfg : rewrite_cfg := {}) : conv unit :=
rw_core q.rules cfg
end rw

end interactive
end conv

namespace tactic
namespace interactive
open lean
open lean.parser
open interactive
open interactive.types
open tactic
local postfix `?`:9001 := optional

private meta def conv_at (h_name : name) (c : conv unit) : tactic unit :=
do h ← get_local h_name,
   h_type ← infer_type h,
   (new_h_type, pr) ← c.convert h_type,
   replace_hyp h new_h_type pr,
   return ()

private meta def conv_target (c : conv unit) : tactic unit :=
do t ← target,
   (new_t, pr) ← c.convert t,
   replace_target new_t pr,
   try tactic.triv, try (tactic.reflexivity reducible)

meta def conv (loc : parse (tk "at" *> ident)?)
              (p : parse (tk "in" *> parser.pexpr)?)
              (c : conv.interactive.itactic) : tactic unit :=
do let c :=
       match p with
       | some p := _root_.conv.interactive.find p c
       | none   := c
       end,
   match loc with
   | some h := conv_at h c
   | none   := conv_target c
   end

end interactive
end tactic
