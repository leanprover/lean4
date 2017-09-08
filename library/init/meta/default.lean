/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.name init.meta.options init.meta.format init.meta.rb_map
import init.meta.level init.meta.expr init.meta.environment init.meta.attribute
import init.meta.tactic init.meta.contradiction_tactic init.meta.constructor_tactic
import init.meta.injection_tactic init.meta.relation_tactics init.meta.fun_info
import init.meta.congr_lemma init.meta.match_tactic init.meta.ac_tactics
import init.meta.backward init.meta.rewrite_tactic
import init.meta.derive init.meta.mk_dec_eq_instance
import init.meta.simp_tactic init.meta.set_get_option_tactics
import init.meta.interactive init.meta.converter init.meta.vm
import init.meta.comp_value_tactics init.meta.smt
import init.meta.async_tactic init.meta.ref init.meta.coinductive_predicates
import init.meta.hole_command init.meta.congr_tactic
