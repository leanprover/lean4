/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic

/- Congruence closure state -/
meta constant cc_state              : Type
meta constant cc_state.mk           : cc_state
/- Create a congruence closure state object using the hypotheses in the current goal. -/
meta constant cc_state.mk_using_hs  : tactic cc_state
meta constant cc_state.next         : cc_state → expr → expr
meta constant cc_state.inconsistent : cc_state → bool
meta constant cc_state.roots        : cc_state → list expr
meta constant cc_state.root         : cc_state → expr → expr
meta constant cc_state.mt           : cc_state → expr → nat
meta constant cc_state.is_cg_root   : cc_state → expr → bool
meta constant cc_state.pp_eqc       : cc_state → expr → tactic format
meta constant cc_state.pp           : cc_state → tactic format
meta constant cc_state.internalize  : cc_state → expr → bool → tactic cc_state
meta constant cc_state.add          : cc_state → expr → tactic cc_state
meta constant cc_state.is_eqv       : cc_state → expr → expr → tactic bool
meta constant cc_state.is_not_eqv   : cc_state → expr → expr → tactic bool
meta constant cc_state.eqv_proof    : cc_state → expr → expr → tactic expr
