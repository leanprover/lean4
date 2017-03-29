/-
Copyright (c) 2017 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import .superposition
open tactic monad expr

namespace super

meta def is_demodulator (c : clause) : bool :=
match c.get_lits with
| [clause.literal.right eqn] := eqn.is_eq.is_some
| _ := ff
end

variable gt : expr → expr → bool

meta def demod' (cs1 : list derived_clause) : clause → list derived_clause → tactic (list derived_clause × clause) | c2 used_demods :=
(first $ do
  i ← list.range c2.num_lits,
  pos ← rwr_positions c2 i,
  c1 ← cs1,
  (ltr, congr_ax) ← [(tt, ``super.sup_ltr), (ff, ``super.sup_rtl)],
  [do c2' ← try_sup gt c1.c c2 0 i pos ltr tt congr_ax,
      demod' c2' (c1 :: used_demods)]
) <|> return (used_demods, c2)

meta def demod (cs1 : list derived_clause) (c2 : clause) : tactic (list derived_clause × clause) := do
c2qf ← c2.open_constn c2.num_quants,
(used_demods, c2qf') ← demod' gt cs1 c2qf.1 [],
if used_demods.empty then return ([], c2) else
return (used_demods, c2qf'.close_constn c2qf.2)

meta def demod_fwd_inf : inference :=
take given, do
active ← get_active,
demods ← return (do ac ← active.values, guard $ is_demodulator ac.c, guard $ ac.id ≠ given.id, [ac]),
if demods.empty then skip else do
(used_demods, given') ← demod gt demods given.c,
if used_demods.empty then skip else do
remove_redundant given.id used_demods,
mk_derived given' given.sc.sched_now >>= add_inferred

meta def demod_back1 (given active : derived_clause) : prover unit := do
(used_demods, c') ← demod gt [given] active.c,
if used_demods.empty then skip else do
remove_redundant active.id used_demods,
mk_derived c' active.sc.sched_now >>= add_inferred

meta def demod_back_inf : inference :=
take given, if ¬is_demodulator given.c then skip else
do active ← get_active, sequence' $ do
ac ← active.values,
guard $ ac.id ≠ given.id,
[demod_back1 gt given ac]

@[super.inf]
meta def demod_inf : inf_decl := {
  prio := 10,
  inf := take given, do
    gt ← get_term_order,
    demod_fwd_inf gt given,
    demod_back_inf gt given,
    skip
}

end super
