/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include "kernel/expr_pair.h"
#include "library/type_context.h"
#include "library/vm/vm.h"
#include "library/tactic/simp_lemmas.h"
#include "library/tactic/simp_result.h"

namespace lean {

simp_result simplify(type_context & tctx, name const & rel, simp_lemmas const & simp_lemmas, vm_obj const & prove_fn, expr const & e);
simp_result simplify(type_context & tctx, name const & rel, simp_lemmas const & simp_lemmas, expr const & e);

simp_result simplify(type_context & tctx, type_context & tctx_whnf, name const & rel, simp_lemmas const & simp_lemmas, vm_obj const & prove_fn, expr const & e);
simp_result simplify(type_context & tctx, type_context & tctx_whnf, name const & rel, simp_lemmas const & simp_lemmas, expr const & e);

name get_simplify_prefix_name();
name get_simplify_max_steps_name();
name get_simplify_nary_assoc_name();
name get_simplify_memoize_name();
name get_simplify_contextual_name();
name get_simplify_rewrite_name();
name get_simplify_unsafe_nary_name();
name get_simplify_theory_name();
name get_simplify_topdown_name();
name get_simplify_lift_eq_name();
name get_simplify_canonize_instances_fixed_point_name();
name get_simplify_canonize_proofs_fixed_point_name();
name get_simplify_canonize_subsingletons_name();

void initialize_simplifier();
void finalize_simplifier();

}
