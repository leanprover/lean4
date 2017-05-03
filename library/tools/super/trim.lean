/-
Copyright (c) 2016 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import .utils
open monad expr tactic

namespace super

-- TODO(gabriel): rewrite using conversions
meta def trim : expr → tactic expr
| (app (lam n m d b) arg) :=
  if ¬b.has_var then
    trim b
  else
    lift₂ app (trim (lam n m d b)) (trim arg)
| (app a b) := lift₂ app (trim a) (trim b)
| (lam n m d b) := do
  x ← mk_local' `x m d,
  b' ← trim (instantiate_var b x),
  return $ lam n m d (abstract_local b' x.local_uniq_name)
| (elet n t v b) :=
  if has_var b then do
    x ← mk_local_def `x t,
    b' ← trim (instantiate_var b x),
    return $ elet n t v (abstract_local b' x.local_uniq_name)
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
  done,
  set_goals (g::gs),
  instantiate_mvars g' >>= trim' >>= exact,
  return r
| [] := fail "no goal"
end

end super
