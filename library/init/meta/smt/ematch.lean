/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.smt.congruence_closure
open tactic

/- Heuristic instantiation lemma -/
meta constant hinst_lemma : Type

meta constant hinst_lemmas : Type

/- (mk_core m e as_simp), m is used to decide which definitions will be unfolded in patterns.
   If as_simp is tt, then this tactic will try to use the left-hand-side of the conclusion
   as a pattern. -/
meta constant hinst_lemma.mk_core           : transparency → expr → bool → tactic hinst_lemma
meta constant hinst_lemma.mk_from_decl_core : transparency → name → bool → tactic hinst_lemma
meta constant hinst_lemma.pp                : hinst_lemma → tactic format
meta constant hinst_lemma.id                : hinst_lemma → name

meta def hinst_lemma.mk (h : expr) : tactic hinst_lemma :=
hinst_lemma.mk_core reducible h ff

meta def hinst_lemma.mk_from_decl (h : name) : tactic hinst_lemma :=
hinst_lemma.mk_from_decl_core reducible h ff

meta constant hinst_lemmas.mk              : hinst_lemmas
meta constant hinst_lemmas.add             : hinst_lemmas → hinst_lemma → hinst_lemmas
meta constant hinst_lemmas.fold {α : Type} : hinst_lemmas → α → (hinst_lemma → α → α) → α

meta def hinst_lemmas.pp (s : hinst_lemmas) : tactic format :=
let tac := s^.fold (return format.nil)
    (λ h tac, do
      hpp ← h^.pp,
      r   ← tac,
      if r^.is_nil then return hpp
      else return (r ++ to_fmt "," ++ format.line ++ hpp))
in do
  r ← tac,
  return $ format.cbrace (format.group r)

structure ematch_config :=
(max_instances : nat)

def default_ematch_config : ematch_config :=
{max_instances := 10000}

/- Ematching -/
meta constant ematch_state             : Type
meta constant ematch_state.mk          : ematch_config → ematch_state
meta constant ematch_state.internalize : ematch_state → expr → tactic ematch_state

namespace tactic
meta constant ematch_core       : transparency → cc_state → ematch_state → hinst_lemma → expr → tactic (list (expr × expr) × cc_state × ematch_state)
meta constant ematch_all_core   : transparency → cc_state → ematch_state → hinst_lemma → bool → tactic (list (expr × expr) × cc_state × ematch_state)

meta def ematch : cc_state → ematch_state → hinst_lemma → expr → tactic (list (expr × expr) × cc_state × ematch_state) :=
ematch_core reducible

meta def ematch_all : cc_state → ematch_state → hinst_lemma → bool → tactic (list (expr × expr) × cc_state × ematch_state) :=
ematch_all_core reducible
end tactic
