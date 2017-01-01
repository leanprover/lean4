/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic init.meta.set_get_option_tactics

structure cc_config :=
/- If tt, congruence closure will treat implicit instance arguments as constants. -/
(ignore_instances : bool)
/- If tt, congruence closure modulo AC. -/
(ac               : bool)
/- If ho_fns is (some fns), then full (and more expensive) support for higher-order functions is
   *only* considered for the functions in fns and local functions. The performance overhead is described in the paper
   "Congruence Closure in Intensional Type Theory". If ho_fns is none, then full support is provided
   for *all* constants. -/
(ho_fns           : option (list name))

def default_cc_config : cc_config :=
{ignore_instances := tt, ac := tt, ho_fns := some []}

/- Congruence closure state -/
meta constant cc_state                  : Type
meta constant cc_state.mk_core          : cc_config → cc_state
/- Create a congruence closure state object using the hypotheses in the current goal. -/
meta constant cc_state.mk_using_hs_core : cc_config → tactic cc_state
meta constant cc_state.next             : cc_state → expr → expr
meta constant cc_state.roots_core       : cc_state → bool → list expr
meta constant cc_state.root             : cc_state → expr → expr
meta constant cc_state.mt               : cc_state → expr → nat
meta constant cc_state.gmt              : cc_state → nat
meta constant cc_state.inc_gmt          : cc_state → cc_state
meta constant cc_state.is_cg_root       : cc_state → expr → bool
meta constant cc_state.pp_eqc           : cc_state → expr → tactic format
meta constant cc_state.pp_core          : cc_state → bool → tactic format
meta constant cc_state.internalize      : cc_state → expr → bool → tactic cc_state
meta constant cc_state.add              : cc_state → expr → tactic cc_state
meta constant cc_state.is_eqv           : cc_state → expr → expr → tactic bool
meta constant cc_state.is_not_eqv       : cc_state → expr → expr → tactic bool
meta constant cc_state.eqv_proof        : cc_state → expr → expr → tactic expr
meta constant cc_state.inconsistent     : cc_state → bool
/- If the given state is inconsistent, return a proof for false. Otherwise fail. -/
meta constant cc_state.false_proof      : cc_state → tactic expr
namespace cc_state

meta def mk : cc_state :=
cc_state.mk_core default_cc_config

meta def mk_using_hs : tactic cc_state :=
cc_state.mk_using_hs_core default_cc_config

meta def roots (s : cc_state) : list expr :=
cc_state.roots_core s tt

meta def pp (s : cc_state) : tactic format :=
cc_state.pp_core s tt

meta def eqc_of_core (s : cc_state) : expr → expr → list expr → list expr
| e f r :=
  let n := s^.next e in
  if n = f then e::r else eqc_of_core n f (e::r)

meta def eqc_of (s : cc_state) (e : expr) : list expr :=
s^.eqc_of_core e e []

meta def in_singlenton_eqc (s : cc_state) (e : expr) : bool :=
to_bool (s^.next e = e)

meta def eqc_size (s : cc_state) (e : expr) : nat :=
(s^.eqc_of e)^.length

end cc_state

open tactic
meta def tactic.cc_core (cfg : cc_config) : tactic unit :=
do intros, s ← cc_state.mk_using_hs_core cfg, t ← target, s ← s^.internalize t tt,
   if s^.inconsistent then do {
     pr ← s^.false_proof,
     mk_app `false.elim [t, pr] >>= exact}
   else do {
     tr ← return $ expr.const `true [],
     b ← s^.is_eqv t tr,
     if b then do {
       pr ← s^.eqv_proof t tr,
       mk_app `of_eq_true [pr] >>= exact
     } else do {
       dbg ← get_bool_option `trace.cc.failure ff,
       if dbg then do {
         ccf ← s^.pp,
         msg ← return $ to_fmt "cc tactic failed, equivalence classes: " ++ format.line ++ ccf,
         fail msg
       } else do {
         fail "cc tactic failed"
       }
     }
   }

meta def tactic.cc : tactic unit :=
tactic.cc_core default_cc_config

meta def tactic.cc_dbg_core (cfg : cc_config) : tactic unit :=
save_options $
  set_bool_option `trace.cc.failure tt
  >> tactic.cc_core cfg

meta def tactic.cc_dbg : tactic unit :=
tactic.cc_dbg_core default_cc_config

meta def tactic.ac_refl : tactic unit :=
do (lhs, rhs) ← target >>= match_eq,
   s ← return $ cc_state.mk,
   s ← s^.internalize lhs ff,
   s ← s^.internalize rhs ff,
   b ← s^.is_eqv lhs rhs,
   if b then do {
     t ← return $ expr.const `true [],
     s^.eqv_proof lhs rhs >>= exact
   } else do {
     fail "ac_refl failed"
   }

/- Heuristic instantiation lemma -/
meta constant hinst_lemma : Type

/- (mk_core m e as_simp prio) -/
meta constant hinst_lemma.mk_core           : transparency → expr → bool → nat → tactic hinst_lemma
meta constant hinst_lemma.mk_from_decl_core : transparency → name → bool → nat → tactic hinst_lemma
meta constant hinst_lemma.pp                : hinst_lemma → tactic format

meta def hinst_lemma.mk (h : expr) : tactic hinst_lemma :=
hinst_lemma.mk_core semireducible h ff 0

meta def hinst_lemma.mk_from_decl (h : name) : tactic hinst_lemma :=
hinst_lemma.mk_from_decl_core semireducible h ff 0

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
