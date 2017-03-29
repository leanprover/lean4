/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
-/
prelude
import init.meta.tactic init.meta.simp_tactic init.meta.rewrite_tactic init.meta.converter init.function

namespace inductive_compiler
namespace tactic

open tactic list

private meta def simp_assumption (ls : simp_lemmas) (e : expr) : tactic (expr × expr) := do
  (a, new_e, pf) ← ext_simplify_core () {} ls (λ u, failed)
                                              (λ a s r p e, failed)
                                              (λ a s r p e, do ⟨u, new_e, pr⟩ ← conv.apply_lemmas_core s assumption r e,
                                                            return ((), new_e, pr, tt))
                                     `iff e,
  return (new_e, pf)


private meta def simp_at_assumption (S : simp_lemmas := simp_lemmas.mk) (h : expr) (extra_lemmas : list expr := []) (cfg : simp_config := {}) : tactic unit :=
do when (expr.is_local_constant h = ff) (fail "tactic fsimp_at failed, the given expression is not a hypothesis"),
   htype ← infer_type h,
   S     ← S.append extra_lemmas,
   (new_htype, heq) ← simp_assumption S htype,
   assert (expr.local_pp_name h) new_htype,
   mk_app `iff.mp [heq, h] >>= exact,
   try $ clear h

private meta def fsimp (extra_lemmas : list expr := []) (cfg : simp_config := {}) : tactic unit :=
do S ← return (simp_lemmas.mk),
   S ← S.append extra_lemmas,
   simplify_goal S cfg >> try triv >> try (reflexivity reducible)

private meta def at_end (e : expr) : ℕ → tactic (list (option expr))
| 0 := fail "at_end expected arity > 0"
| 1 := return [some e]
| (n+1) := at_end n >>= (λ xs, return (none :: xs))

private meta def heq_to_eq_or_id (n : name) (H : expr) : tactic expr := do
  Ht ← infer_type H,
  do {
    (A, lhs, B, rhs) ← match_heq Ht,
    unify A B,
    heq ← mk_app `eq [lhs, rhs],
    pr  ← mk_app `eq_of_heq [H],
    assertv n heq pr,
    clear H,
    get_local n }
  <|>
  return H

private meta def intros_simp (inj_simps : simp_lemmas) : expr → tactic (list expr)
| (expr.pi n bi b d) := do
  H ← intro n,
--  H ← heq_to_eq_or_id n H,
  try $ simp_at_assumption inj_simps H,
  H ← get_local n,
  tgt ← target,
  rest ← intros_simp tgt,
  return (H :: rest)

| e           := do return []

private meta def prove_conjuncts_by_assumption : list expr → expr → tactic unit
| (pf :: pfs) ```(and %%α %%β) := do
    split,
    exact pf,
    prove_conjuncts_by_assumption pfs β

| [pf] _ := exact pf

| _ _ := fail "expecting same number of proofs as conjuncts"

private meta def intros_and_subst : expr → tactic unit
| (expr.pi n bi b d) := do
  H ← intro n,
  H ← heq_to_eq_or_id n H,
  Ht ← infer_type H,
  try $ do {
    match_eq Ht,
    subst H },
  target >>= intros_and_subst

| e           := return ()

private meta def tgt_to_eq : tactic unit := do
  tgt ← target,
  try (do c ← mk_const `heq_of_eq, apply c)

meta def prove_nested_inj (inj_simps : simp_lemmas) (inner_ir_inj_arrow : name) : tactic unit := do
  xs ← intros,
  triv <|> solve1 (do
  H_orig_eq ← return (ilast xs),
  c ← mk_const inner_ir_inj_arrow,
  inner_inj ← to_expr `(%%c %%H_orig_eq),
  apply inner_inj,
  pfs ← (target >>= intros_simp inj_simps),
  target >>= prove_conjuncts_by_assumption pfs)

meta def prove_pack_inj (unpack unpack_pack : name) : tactic unit := do
  target >>= intros_and_subst,
  split,
  -- prove easy direction first
  swap,
  solve1 (do H ← intro1, H ← heq_to_eq_or_id `H_rhs_eq H, fsimp [H]),
  -- hard direction
  H ← intro1,
  H ← heq_to_eq_or_id `H_lhs_eq H,
  tgt_to_eq,
  Ht ← infer_type H,
  (lhs, rhs) ← match_eq Ht,
  arity ← return (expr.get_app_num_args lhs),
  args1 ← at_end lhs arity,
  args2 ← at_end rhs arity,
  lhs' ← mk_mapp unpack args1,
  rhs' ← mk_mapp unpack args2,
  H_ty ← mk_app `eq [lhs', rhs'],
  assert `H_up H_ty,
  solve1 (fsimp [H]),
  H_up ← get_local `H_up,
  solve1 (do e_unpack_pack ← mk_const unpack_pack,
             rewrite_at_core semireducible tt tt occurrences.all ff e_unpack_pack H_up,
             H_up ← get_local `H_up,
             rewrite_at_core semireducible tt tt occurrences.all ff e_unpack_pack H_up,
             H_up ← get_local `H_up,
             exact H_up)

end tactic
end inductive_compiler
