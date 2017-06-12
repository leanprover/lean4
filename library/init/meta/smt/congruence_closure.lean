/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.interactive_base init.meta.tactic init.meta.set_get_option_tactics

structure cc_config :=
/- If tt, congruence closure will treat implicit instance arguments as constants. -/
(ignore_instances : bool               := tt)
/- If tt, congruence closure modulo AC. -/
(ac               : bool               := tt)
/- If ho_fns is (some fns), then full (and more expensive) support for higher-order functions is
   *only* considered for the functions in fns and local functions. The performance overhead is described in the paper
   "Congruence Closure in Intensional Type Theory". If ho_fns is none, then full support is provided
   for *all* constants. -/
(ho_fns           : option (list name) := none)
/- If true, then use excluded middle -/
(em               : bool               := tt)

/-- Congruence closure state -/
meta constant cc_state                  : Type
meta constant cc_state.mk_core          : cc_config → cc_state
/-- Create a congruence closure state object using the hypotheses in the current goal. -/
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
meta constant cc_state.internalize      : cc_state → expr → tactic cc_state
meta constant cc_state.add              : cc_state → expr → tactic cc_state
meta constant cc_state.is_eqv           : cc_state → expr → expr → tactic bool
meta constant cc_state.is_not_eqv       : cc_state → expr → expr → tactic bool
meta constant cc_state.eqv_proof        : cc_state → expr → expr → tactic expr
meta constant cc_state.inconsistent     : cc_state → bool
/-- `proof_for cc e` constructs a proof for e if it is equivalent to true in cc_state -/
meta constant cc_state.proof_for        : cc_state → expr → tactic expr
/-- `refutation_for cc e` constructs a proof for `not e` if it is equivalent to false in cc_state -/
meta constant cc_state.refutation_for   : cc_state → expr → tactic expr
/-- If the given state is inconsistent, return a proof for false. Otherwise fail. -/
meta constant cc_state.proof_for_false  : cc_state → tactic expr
namespace cc_state

meta def mk : cc_state :=
cc_state.mk_core {}

meta def mk_using_hs : tactic cc_state :=
cc_state.mk_using_hs_core {}

meta def roots (s : cc_state) : list expr :=
cc_state.roots_core s tt

meta instance : has_to_tactic_format cc_state :=
⟨λ s, cc_state.pp_core s tt⟩

meta def eqc_of_core (s : cc_state) : expr → expr → list expr → list expr
| e f r :=
  let n := s.next e in
  if n = f then e::r else eqc_of_core n f (e::r)

meta def eqc_of (s : cc_state) (e : expr) : list expr :=
s.eqc_of_core e e []

meta def in_singlenton_eqc (s : cc_state) (e : expr) : bool :=
s.next e = e

meta def eqc_size (s : cc_state) (e : expr) : nat :=
(s.eqc_of e).length

meta def fold_eqc_core {α} (s : cc_state) (f : α → expr → α) (first : expr) : expr → α → α
| c a :=
  let new_a := f a c,
      next  := s.next c in
  if next =ₐ first then new_a
  else fold_eqc_core next new_a

meta def fold_eqc {α} (s : cc_state) (e : expr) (a : α) (f : α → expr → α) : α :=
fold_eqc_core s f e e a

meta def mfold_eqc {α} {m : Type → Type} [monad m] (s : cc_state) (e : expr) (a : α) (f : α → expr → m α) : m α :=
fold_eqc s e (return a) (λ act e, do a ← act, f a e)
end cc_state

open tactic
meta def tactic.cc_core (cfg : cc_config) : tactic unit :=
do intros, s ← cc_state.mk_using_hs_core cfg, t ← target, s ← s.internalize t,
   if s.inconsistent then do {
     pr ← s.proof_for_false,
     mk_app `false.elim [t, pr] >>= exact}
   else do {
     tr ← return $ expr.const `true [],
     b ← s.is_eqv t tr,
     if b then do {
       pr ← s.eqv_proof t tr,
       mk_app `of_eq_true [pr] >>= exact
     } else do {
       dbg ← get_bool_option `trace.cc.failure ff,
       if dbg then do {
         ccf ← pp s,
         fail format!"cc tactic failed, equivalence classes: \n{ccf}"
       } else do {
         fail "cc tactic failed"
       }
     }
   }

meta def tactic.cc : tactic unit :=
tactic.cc_core {}

meta def tactic.cc_dbg_core (cfg : cc_config) : tactic unit :=
save_options $
  set_bool_option `trace.cc.failure tt
  >> tactic.cc_core cfg

meta def tactic.cc_dbg : tactic unit :=
tactic.cc_dbg_core {}

meta def tactic.ac_refl : tactic unit :=
do (lhs, rhs) ← target >>= match_eq,
   s ← return $ cc_state.mk,
   s ← s.internalize lhs,
   s ← s.internalize rhs,
   b ← s.is_eqv lhs rhs,
   if b then do {
     s.eqv_proof lhs rhs >>= exact
   } else do {
     fail "ac_refl failed"
   }
