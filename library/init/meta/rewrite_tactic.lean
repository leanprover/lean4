/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.relation_tactics init.meta.occurrences

namespace tactic
/-- Configuration options for the `rewrite` tactic. -/
structure rewrite_cfg extends apply_cfg :=
(md            := reducible)
(symm          := ff)
(occs          := occurrences.all)

/-- Rewrite the expression `e` using `h`.
    The unification is performed using the transparency mode in `cfg`.
    If `cfg.approx` is `tt`, then fallback to first-order unification, and approximate context during unification.
    `cfg.new_goals` specifies which unassigned metavariables become new goals, and their order.
    If `cfg.instances` is `tt`, then use type class resolution to instantiate unassigned meta-variables.
    The fields `cfg.auto_param` and `cfg.opt_param` are ignored by this tactic (See `tactic.rewrite`).
    It a triple `(new_e, prf, metas)` where `prf : e = new_e`, and `metas` is a list of all introduced meta variables,
    even the assigned ones.

    TODO(Leo): improve documentation and explain symm/occs -/
meta constant rewrite_core (h : expr) (e : expr) (cfg : rewrite_cfg := {}) : tactic (expr × expr × list expr)

meta def rewrite (h : expr) (e : expr) (cfg : rewrite_cfg := {}) : tactic (expr × expr × list expr) :=
do (new_t, prf, metas) ← rewrite_core h e cfg,
   try_apply_opt_auto_param cfg.to_apply_cfg metas,
   return (new_t, prf, metas)

meta def rewrite_target (h : expr) (cfg : rewrite_cfg := {}) : tactic unit :=
do t ← target,
   (new_t, prf, _) ← rewrite h t cfg,
   replace_target new_t prf

meta def rewrite_hyp (h : expr) (hyp : expr) (cfg : rewrite_cfg := {}) : tactic expr :=
do hyp_type ← infer_type hyp,
   (new_hyp_type, prf, _) ← rewrite h hyp_type cfg,
   replace_hyp hyp new_hyp_type prf

end tactic
