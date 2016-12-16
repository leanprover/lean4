import .utils
open monad expr tactic

namespace super

meta def count_var_occs : unsigned → expr → ℕ
| k (var k')              := if k = k' then 1 else 0
| _ (sort _)              := 0
| _ (const _ _)           := 0
| _ (mvar _ _)            := 0
| k (local_const _ _ _ t) := count_var_occs k t
| k (app a b)             := count_var_occs k a + count_var_occs k b
| k (lam _ _ t b)         := count_var_occs k t + count_var_occs k^.succ b
| k (pi _ _ t b)          := count_var_occs k t + count_var_occs k^.succ b
| k (elet _ t v b)        := count_var_occs k t + count_var_occs k v + count_var_occs k^.succ b
| _ (macro _ _ _)         := 0 -- TODO(gabriel)

-- TODO(gabriel): rewrite using conversions
meta def trim : expr → tactic expr
| (app (lam n m d b) arg) :=
  if has_var b = ff ∨ count_var_occs 0 b ≤ 1 then
    trim (instantiate_var b arg)
  else
    lift₂ app (trim (lam n m d b)) (trim arg)
| (app a b) := lift₂ app (trim a) (trim b)
| (lam n m d b) := do
  x ← mk_local' `x m d,
  b' ← trim (instantiate_var b x),
  return $ lam n m d (abstract_local b' x^.local_uniq_name)
| (elet n t v b) :=
  if has_var b then do
    x ← mk_local_def `x t,
    b' ← trim (instantiate_var b x),
    return $ elet n t v (abstract_local b' x^.local_uniq_name)
  else
    trim b
| e := return e

-- iterate trim until convergence
meta def trim' : expr → tactic expr
| e := do e' ← trim e,
          if e =ₐ e' then
            return e
          else
            trim' e'

open tactic

meta def with_trim {α} (tac : tactic α) : tactic α := do
gs ← get_goals,
match gs with
| (g::gs) := do
  g' ← infer_type g >>= mk_meta_var,
  set_goals [g'],
  r ← tac,
  now,
  set_goals (g::gs),
  instantiate_mvars g' >>= trim' >>= exact,
  return r
| [] := fail "no goal"
end

end super
