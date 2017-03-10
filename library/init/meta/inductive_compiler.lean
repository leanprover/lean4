/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
-/
prelude
import init.meta.tactic init.meta.simp_tactic init.meta.rewrite_tactic init.function

namespace inductive_compiler
namespace tactic

open tactic list

private meta def fsimplify (S : simp_lemmas) (e : expr) (cfg : simp_config := {}) : tactic (expr × expr) :=
do e_type       ← infer_type e >>= whnf,
   simplify_core cfg S `iff e

private meta def fsimp_at (S : simp_lemmas := simp_lemmas.mk) (h : expr) (extra_lemmas : list expr := []) (cfg : simp_config := {}) : tactic unit :=
do when (expr.is_local_constant h = ff) (fail "tactic fsimp_at failed, the given expression is not a hypothesis"),
   htype ← infer_type h,
   S     ← S^.append extra_lemmas,
   (new_htype, heq) ← fsimplify S htype cfg,
   assert (expr.local_pp_name h) new_htype,
   mk_app `iff.mp [heq, h] >>= exact,
   try $ clear h

private meta def fsimp (extra_lemmas : list expr := []) (cfg : simp_config := {}) : tactic unit :=
do S ← return (simp_lemmas.mk),
   S ← S^.append extra_lemmas,
   simplify_goal S cfg >> try triv >> try (reflexivity reducible)

private meta def at_end (e : expr) : ℕ → tactic (list (option expr))
| 0 := fail "at_end expected arity > 0"
| 1 := return [some e]
| (n+1) := at_end n >>= (λ xs, return (none :: xs))

private meta def intros_simp_and_subst (inj_simps : simp_lemmas) : expr → tactic unit
| (expr.pi n bi b d) := do
  H ← intro n,
  Ht ← infer_type H,
  try $ do {
    (A, lhs, B, rhs) ← match_heq Ht,
    unify A B,
    heq ← mk_app `eq [lhs, rhs],
    pr  ← mk_app `eq_of_heq [H],
    assertv n heq pr,
    clear H },
  H ← get_local n,
  try $ fsimp_at inj_simps H,
  H ← get_local n,
  -- TODO(dhs): this may be a performance problem in the future
  -- We need it now because the simp rules (pack x1 y1 = pack x2 y2 <-> y1 == y2) have eq on the LHS.
  -- To avoid subst here, we may need to subst in the proof of the pack injectivity lemmas.
  subst H,
  tgt ← target,
  intros_simp_and_subst tgt

| e           := do skip

private meta def prove_conjuncts_by_reflexivity : expr → tactic unit
| ```(and %%α %%β) := do
    split,
    reflexivity,
    prove_conjuncts_by_reflexivity β
| _ := reflexivity

meta def prove_nested_inj (inj_simps : simp_lemmas) (inner_ir_inj_arrow : name) : tactic unit := do
  xs ← intros,
  triv <|> solve1 (do
  H_orig_eq ← return (ilast xs),
  c ← mk_const inner_ir_inj_arrow,
  inner_inj ← to_expr `(%%c %%H_orig_eq),
  apply inner_inj,
  target >>= intros_simp_and_subst inj_simps,
  target >>= prove_conjuncts_by_reflexivity)

meta def prove_pack_inj (unpack unpack_pack : name) : tactic unit := do
  intros, split,
  -- prove easy direction first
  swap,
  solve1 (do H ← intro1, fsimp [H]),
  -- hard direction
  H ← intro1,
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
