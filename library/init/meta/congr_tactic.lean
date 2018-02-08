/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
-/
prelude
import init.meta.tactic init.meta.congr_lemma init.meta.relation_tactics init.function

namespace tactic

meta def apply_congr_core (clemma : congr_lemma) : tactic unit :=
do assert `H_congr_lemma clemma.type,
   exact clemma.proof,
   get_local `H_congr_lemma >>= apply,
   all_goals $ do
     try (applyc `heq_of_eq),
     get_local `H_congr_lemma >>= clear

meta def apply_eq_congr_core (tgt : expr) : tactic unit :=
do (lhs, rhs) ← match_eq tgt,
   guard lhs.is_app,
   clemma ← mk_specialized_congr_lemma lhs,
   apply_congr_core clemma

meta def apply_heq_congr_core : tactic unit :=
do try (applyc `eq_of_heq),
   (α, lhs, β, rhs) ← target >>= match_heq,
   guard lhs.is_app,
   clemma ← mk_hcongr_lemma lhs.get_app_fn lhs.get_app_num_args,
   apply_congr_core clemma

meta def congr_core : tactic unit :=
do tgt ← target,
   apply_eq_congr_core tgt
   <|> apply_heq_congr_core
   <|> fail "congr tactic failed"

meta def congr : tactic unit :=
do focus1 (try assumption >> congr_core >> all_goals (try reflexivity >> try congr))

end tactic
