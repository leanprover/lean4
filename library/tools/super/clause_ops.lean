/-
Copyright (c) 2016 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import .clause data.monad.transformers
open monad tactic expr

namespace super

meta def on_left_at {m} [monad m] (c : clause) (i : ℕ)
                    [has_monad_lift_t tactic m]
                    -- f gets a type and returns a list of proofs of that type
                    (f : expr → m (list (list expr × expr))) : m (list clause) := do
op : clause × list expr ← ♯c^.open_constn (c^.num_quants + i),
♯ @guard tactic _ (op.1^.get_lit 0)^.is_neg _,
new_hyps ← f (op.1^.get_lit 0)^.formula,
return $ new_hyps^.for (λnew_hyp,
  (op.1^.inst new_hyp.2)^.close_constn (op.2 ++ new_hyp.1))

meta def on_left_at_dn {m} [monad m] [alternative m] (c : clause) (i : ℕ)
                    [has_monad_lift_t tactic m]
                    -- f gets a hypothesis of ¬type and returns a list of proofs of false
                    (f : expr → m (list (list expr × expr))) : m (list clause) := do
qf : clause × list expr ← ♯c^.open_constn c^.num_quants,
op : clause × list expr ← ♯qf.1^.open_constn c^.num_lits,
lci ← (op.2^.nth i)^.to_monad,
♯ @guard tactic _ (qf.1^.get_lit i)^.is_neg _,
h ← ♯ mk_local_def `h $ imp (qf.1^.get_lit i)^.formula c^.local_false,
new_hyps ← f h,
return $ new_hyps^.for $ λnew_hyp,
  (((clause.mk 0 0 new_hyp.2 c^.local_false c^.local_false)^.close_const h)^.inst
               (op.1^.close_const lci)^.proof)^.close_constn
  (qf.2 ++ op.2^.remove_nth i ++ new_hyp.1)

meta def on_right_at {m} [monad m] (c : clause) (i : ℕ)
                     [has_monad_lift_t tactic m]
                     -- f gets a hypothesis and returns a list of proofs of false
                     (f : expr → m (list (list expr × expr))) : m (list clause) := do
op : clause × list expr ← ♯c^.open_constn (c^.num_quants + i),
♯ @guard tactic _ ((op.1^.get_lit 0)^.is_pos) _,
h ← ♯ mk_local_def `h (op.1^.get_lit 0)^.formula,
new_hyps ← f h,
return $ new_hyps^.for (λnew_hyp,
  (op.1^.inst (lambdas [h] new_hyp.2))^.close_constn (op.2 ++ new_hyp.1))

meta def on_right_at' {m} [monad m] (c : clause) (i : ℕ)
                     [has_monad_lift_t tactic m]
                     -- f gets a hypothesis and returns a list of proofs
                     (f : expr → m (list (list expr × expr))) : m (list clause) := do
op : clause × list expr ← ♯c^.open_constn (c^.num_quants + i),
♯ @guard tactic _ ((op.1^.get_lit 0)^.is_pos) _,
h ← ♯ mk_local_def `h (op.1^.get_lit 0)^.formula,
new_hyps ← f h,
for new_hyps (λnew_hyp, do
  type ← ♯ infer_type new_hyp.2,
  nh ← ♯ mk_local_def `nh $ imp type c^.local_false,
  return $ (op.1^.inst (lambdas [h] (app nh new_hyp.2)))^.close_constn (op.2 ++ new_hyp.1 ++ [nh]))

meta def on_first_right (c : clause) (f : expr → tactic (list (list expr × expr))) : tactic (list clause) :=
first $ do i ← list.range c^.num_lits, [on_right_at c i f]

meta def on_first_right' (c : clause) (f : expr → tactic (list (list expr × expr))) : tactic (list clause) :=
first $ do i ← list.range c^.num_lits, [on_right_at' c i f]

meta def on_first_left (c : clause) (f : expr → tactic (list (list expr × expr))) : tactic (list clause) :=
first $ do i ← list.range c^.num_lits, [on_left_at c i f]

meta def on_first_left_dn (c : clause) (f : expr → tactic (list (list expr × expr))) : tactic (list clause) :=
first $ do i ← list.range c^.num_lits, [on_left_at_dn c i f]

end super
