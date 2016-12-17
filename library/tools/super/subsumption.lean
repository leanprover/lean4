/-
Copyright (c) 2016 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import .clause .prover_state
open tactic monad

namespace super

private meta def try_subsume_core : list clause.literal → list clause.literal → tactic unit
| [] _ := skip
| small large := first $ do
  i ← small^.zip_with_index, j ← large^.zip_with_index,
  return $ do
    unify_lit i.1 j.1,
    try_subsume_core (small^.remove_nth i.2) (large^.remove_nth j.2)

-- FIXME: this is incorrect if a quantifier is unused
meta def try_subsume (small large : clause) : tactic unit := do
small_open ← clause.open_metan small (clause.num_quants small),
large_open ← clause.open_constn large (clause.num_quants large),
guard $ small^.num_lits ≤ large^.num_lits,
try_subsume_core small_open.1^.get_lits large_open.1^.get_lits

meta def does_subsume (small large : clause) : tactic bool :=
(try_subsume small large >> return tt) <|> return ff

meta def does_subsume_with_assertions (small large : derived_clause) : prover bool := do
if small^.assertions^.subset_of large^.assertions then do
  ♯ does_subsume small^.c large^.c
else
  return ff

meta def any_tt {m : Type → Type} [monad m] (active : rb_map clause_id derived_clause) (pred : derived_clause → m bool) : m bool :=
active^.fold (return ff) $ λk a cont, do
  v ← pred a, if v then return tt else cont

meta def any_tt_list {m : Type → Type} [monad m] {A} (pred : A → m bool) : list A → m bool
| [] := return ff
| (x::xs) := do v ← pred x, if v then return tt else any_tt_list xs

@[super.inf]
meta def forward_subsumption : inf_decl := inf_decl.mk 20 $
take given, do active ← get_active,
sequence' $ do a ← active^.values,
  guard $ a^.id ≠ given^.id,
  return $ do
    ss ← ♯ does_subsume a^.c given^.c,
    if ss
    then remove_redundant given^.id [a]
    else return ()

meta def forward_subsumption_pre : prover unit := preprocessing_rule $ λnew, do
active ← get_active, filter (λn, do
  do ss ← any_tt active (λa,
        if a^.assertions^.subset_of n^.assertions then do
          ♯ does_subsume a^.c n^.c
        else
          -- TODO: move to locked
          return ff),
     return (bnot ss)) new

meta def subsumption_interreduction : list derived_clause → prover (list derived_clause)
| (c::cs) := do
  -- TODO: move to locked
  cs_that_subsume_c ← filter (λd, does_subsume_with_assertions d c) cs,
  if ¬cs_that_subsume_c^.empty then
    -- TODO: update score
    subsumption_interreduction cs
  else do
    cs_not_subsumed_by_c ← filter (λd, lift bnot (does_subsume_with_assertions c d)) cs,
    cs' ← subsumption_interreduction cs_not_subsumed_by_c,
    return (c::cs')
| [] := return []

meta def subsumption_interreduction_pre : prover unit :=
preprocessing_rule $ λnew,
let new' := list.sort_on (λc : derived_clause, c^.c^.num_lits) new in
subsumption_interreduction new'

meta def keys_where_tt {m} {K V : Type} [monad m] (active : rb_map K V) (pred : V → m bool) : m (list K) :=
@rb_map.fold _ _ (m (list K)) active (return []) $ λk a cont, do
  v ← pred a, rest ← cont, return $ if v then k::rest else rest

@[super.inf]
meta def backward_subsumption : inf_decl := inf_decl.mk 20 $ λgiven, do
active ← get_active,
ss ← ♯ keys_where_tt active (λa, does_subsume given^.c a^.c),
sequence' $ do id ← ss, guard (id ≠ given^.id), [remove_redundant id [given]]

end super
