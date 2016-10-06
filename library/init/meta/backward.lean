/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic init.meta.set_get_option_tactics

namespace tactic
meta constant back_lemmas : Type

/- Create a datastructure containing all lemmas tagged as [intro].
   Lemmas are indexed using their head-symbol.
   The head-symbol is computed with respect to the given transparency setting. -/
meta constant mk_back_lemmas_core     : transparency → tactic back_lemmas
/- (back_lemmas_insert_core m lemmas lemma) adds the given lemma to the set back_lemmas.
   It infers the type of the lemma, and uses its head-symbol as an index.
   The head-symbol is computed with respect to the given transparency setting. -/
meta constant back_lemmas_insert_core : transparency → back_lemmas → expr → tactic back_lemmas
/- Return the lemmas that have the same head symbol of the given expression -/
meta constant back_lemmas_find        : back_lemmas → expr → tactic (list expr)

meta def mk_back_lemmas : tactic back_lemmas :=
mk_back_lemmas_core reducible

meta def back_lemmas_insert : back_lemmas → expr → tactic back_lemmas :=
back_lemmas_insert_core reducible


/- (backward_chaining_core t insts max_depth pre_tactic leaf_tactic lemmas): perform backward chaining using
   the lemmas marked as [intro] and extra_lemmas.

   The search maximum depth is \c max_depth.

   Before processing each goal, the tactic pre_tactic is invoked. The possible outcomes are:
      1) it closes the goal
      2) it does nothing, and backward_chaining_core tries applicable lemmas.
      3) it fails, and backward_chaining_core backtracks.

   Whenever no lemma is applicable, the leaf_tactic is invoked, to try to close the goal.
   If insts is tt, then type class resolution is used to discharge goals.

   Remark pre_tactic may also be used to trace the execution of backward_chaining_core -/
meta constant backward_chaining_core : transparency → bool → nat → tactic unit → tactic unit → back_lemmas → tactic unit

meta def back_lemmas_add_extra : transparency → back_lemmas → list expr → tactic back_lemmas
| m bls []      := return bls
| m bls (l::ls) := do
  new_bls ← back_lemmas_insert_core m bls l,
  back_lemmas_add_extra m new_bls ls

meta def back_chaining_core (pre_tactic : tactic unit) (leaf_tactic : tactic unit) (extra_lemmas : list expr) : tactic unit :=
do intro_lemmas ← mk_back_lemmas_core reducible,
   new_lemmas   ← back_lemmas_add_extra reducible intro_lemmas extra_lemmas,
   max ← get_nat_option `back_chaining.max_depth 8,
   backward_chaining_core reducible tt max pre_tactic leaf_tactic new_lemmas

meta def back_chaining : tactic unit :=
back_chaining_core skip assumption []

meta def back_chaining_using : list expr → tactic unit :=
back_chaining_core skip assumption

meta def back_chaining_using_hs : tactic unit :=
local_context >>= back_chaining_core skip failed

end tactic
