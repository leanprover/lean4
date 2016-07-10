/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic

namespace tactic
/- (backward_chaining_core t insts max_depth pre_tactic leaf_tactic extra_lemmas): perform backward chaining using
   the lemmas marked as [intro] and extra_lemmas.

   The search maximum depth is \c max_depth.

   Before processing each goal, the tactic pre_tactic is invoked. The possible outcomes are:
      1) it closes the goal
      2) it does nothing, and backward_chaining_core tries applicable lemmas.
      3) it fails, and backward_chaining_core backtracks.

   Whenever no lemma is applicable, the leaf_tactic is invoked, to try to close the goal.
   If insts is tt, then type class resolution is used to discharge goals.

   Remark pre_tactic may also be used to trace the execution of backward_chaining_core -/
meta_constant backward_chaining_core : transparency → bool → nat → tactic unit → tactic unit → list expr → tactic unit

meta_definition back_chaining_core (pre_tactic : tactic unit) (leaf_tactic : tactic unit) (extra_lemmas : list expr) : tactic unit :=
do max ← get_nat_option ("back_chaining" <.> "max_depth") 8,
   backward_chaining_core reducible tt max pre_tactic leaf_tactic extra_lemmas

meta_definition back_chaining : tactic unit :=
back_chaining_core skip assumption []

meta_definition back_chaining_using : list expr → tactic unit :=
back_chaining_core skip assumption

meta_definition back_chaining_using_hs : tactic unit :=
local_context >>= back_chaining_core skip failed

end tactic
