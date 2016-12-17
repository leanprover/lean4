/-
Copyright (c) 2016 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import .clause .prover_state .utils
open tactic monad

namespace super

variable gt : expr → expr → bool
variables (ac1 ac2 : derived_clause)
variables (c1 c2 : clause)
variables (i1 i2 : nat)

-- c1 : ... → ¬a → ...
-- c2 : ... →  a → ...
meta def try_resolve : tactic clause := do
qf1 ← c1↣open_metan c1↣num_quants,
qf2 ← c2↣open_metan c2↣num_quants,
-- FIXME: using default transparency unifies m*n with (x*y*z)*w here ???
unify_core transparency.reducible (qf1↣1↣get_lit i1)↣formula (qf2↣1↣get_lit i2)↣formula,
qf1i ← qf1↣1↣inst_mvars,
guard $ clause.is_maximal gt qf1i i1,
op1 ← qf1↣1↣open_constn i1,
op2 ← qf2↣1↣open_constn c2↣num_lits,
a_in_op2 ← (op2↣2↣nth i2)↣to_monad,
clause.meta_closure (qf1.2 ++ qf2.2) $
  (op1↣1↣inst (op2↣1↣close_const a_in_op2)↣proof)↣close_constn (op1↣2 ++ op2↣2↣remove_nth i2)

meta def try_add_resolvent : prover unit := do
c' ← ♯ try_resolve gt ac1↣c ac2↣c i1 i2,
inf_score 1 [ac1↣sc, ac2↣sc] >>= mk_derived c' >>= add_inferred

meta def maybe_add_resolvent : prover unit :=
try_add_resolvent gt ac1 ac2 i1 i2 <|> return ()

meta def resolution_left_inf : inference :=
take given, do active ← get_active, sequence' $ do
  given_i ← given↣selected,
  guard $ clause.literal.is_neg (given↣c↣get_lit given_i),
  other ← rb_map.values active,
  guard $ ¬given↣sc↣in_sos ∨ ¬other↣sc↣in_sos,
  other_i ← other↣selected,
  guard $ clause.literal.is_pos (other↣c↣get_lit other_i),
  [maybe_add_resolvent gt other given other_i given_i]

meta def resolution_right_inf : inference :=
take given, do active ← get_active, sequence' $ do
  given_i ← given↣selected,
  guard $ clause.literal.is_pos (given↣c↣get_lit given_i),
  other ← rb_map.values active,
  guard $ ¬given↣sc↣in_sos ∨ ¬other↣sc↣in_sos,
  other_i ← other↣selected,
  guard $ clause.literal.is_neg (other↣c↣get_lit other_i),
  [maybe_add_resolvent gt given other given_i other_i]

@[super.inf]
meta def resolution_inf : inf_decl := inf_decl.mk 40 $
take given, do gt ← get_term_order, resolution_left_inf gt given >> resolution_right_inf gt given

end super
