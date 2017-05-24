/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta init.data.sigma.lex init.data.nat.lemmas init.data.list.instances

namespace well_founded_tactics
open tactic

private meta def clear_wf_rec_goal_aux : list expr → tactic unit
| []      := return ()
| (h::hs) := clear_wf_rec_goal_aux hs >> try (guard (h.local_pp_name.is_internal || h.is_aux_decl) >> clear h)

meta def clear_internals : tactic unit :=
local_context >>= clear_wf_rec_goal_aux

meta def unfold_wf_rel : tactic unit :=
dunfold [``has_well_founded.r]

meta def is_psigma_mk : expr → tactic (expr × expr)
| `(psigma.mk %%a %%b) := return (a, b)
| _                    := failed

meta def process_lex : tactic unit → tactic unit
| tac :=
  do t ← target >>= whnf,
  if t.is_napp_of `psigma.lex 6 then
     let a := t.app_fn.app_arg in
     let b := t.app_arg in
     do (a₁, a₂) ← is_psigma_mk a,
        (b₁, b₂) ← is_psigma_mk b,
        (is_def_eq a₁ b₁ >> `[apply psigma.lex.right] >> process_lex tac)
        <|>
        (`[apply psigma.lex.left] >> tac)
  else
     tac

private meta def unfold_sizeof_measure : tactic unit :=
dunfold [``sizeof_measure, ``measure, ``inv_image]

private meta def add_simps : simp_lemmas → list name → tactic simp_lemmas
| s []      := return s
| s (n::ns) := do s' ← s.add_simp n, add_simps s' ns

private meta def collect_sizeof_lemmas (e : expr) : tactic simp_lemmas :=
e.mfold simp_lemmas.mk $ λ c d s,
  if c.is_constant then
    match c.const_name with
    | name.mk_string "sizeof" p :=
      do eqns ← get_eqn_lemmas_for tt c.const_name,
         add_simps s eqns
    | _ := return s
    end
  else
    return s

private meta def unfold_sizeof_loop : tactic unit :=
do
  dunfold [``sizeof, ``has_sizeof.sizeof],
  S ← target >>= collect_sizeof_lemmas,
  (simplify_goal S >> unfold_sizeof_loop)
  <|>
  try simp

meta def unfold_sizeof : tactic unit :=
unfold_sizeof_measure >> unfold_sizeof_loop

meta def default_dec_tac : tactic unit :=
do clear_internals,
   unfold_wf_rel,
   process_lex (unfold_sizeof >> try assumption >> try `[apply nat.lt_succ_self])

end well_founded_tactics

/-- Argument for using_well_founded -/
meta structure well_founded_tactics :=
(rel_tac : tactic unit := tactic.apply_instance)
(dec_tac : tactic unit := well_founded_tactics.default_dec_tac)

meta def well_founded_tactics.default : well_founded_tactics :=
{}
