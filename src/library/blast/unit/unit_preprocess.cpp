/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/inductive/inductive.h"
#include "library/constants.h"
#include "library/util.h"
#include "library/blast/blast.h"
#include "library/blast/action_result.h"
#include "library/blast/unit/unit_actions.h"
#include "library/blast/proof_expr.h"
#include "library/blast/choice_point.h"
#include "library/blast/hypothesis.h"
#include "library/blast/util.h"
#include "library/blast/simplifier/simp_rule_set.h"
#include "library/blast/simplifier/simplifier.h"
#include "library/expr_lt.h"
#include "util/rb_multi_map.h"

namespace lean {
namespace blast {

static name * g_simplify_unit_simp_namespace = nullptr;
static name * g_simplify_contextual          = nullptr;

static bool is_propositional(expr const & e) {
    // TODO(dhs): This predicate will need to evolve, and will eventually be thrown out
    // when we re-implement this module without relying on the simplifier.
    if (!is_prop(e)) return false;
    if (is_pi(e) && closed(binding_body(e))) return true;
    if (is_and(e) || is_or(e) || is_not(env(), e) || is_ite(e) || is_iff(e)) return true;
    return false;
}

action_result unit_preprocess(unsigned hidx) {
    // TODO(dhs, leo): do not rely on the simplifier, and provide a "safe mode" where we
    // introduce auxiliary hypotheses
    state & s            = curr_state();
    if (s.has_target_forward_deps(hidx)) {
        // We currently do not try to simplify a hypothesis if other
        // hypotheses or target depends on it.
        return action_result::failed();
    }
    hypothesis const & h = s.get_hypothesis_decl(hidx);
    if (!is_prop(h.get_type())) {
        // We currently only simplify propositions.
        return action_result::failed();
    }

    simp_rule_sets srss = get_simp_rule_sets(env(), ios().get_options(), *g_simplify_unit_simp_namespace);
    // TODO(dhs): disable contextual rewriting
    auto r = simplify(get_iff_name(), h.get_type(), srss, is_propositional);

    if (r.get_new() == h.get_type()) return action_result::failed(); // did nothing
    expr new_h_proof;
    if (r.has_proof()) {
        new_h_proof = get_app_builder().mk_app(get_iff_mp_name(), r.get_proof(), h.get_self());
    } else {
        // they are definitionally equal
        new_h_proof = h.get_self();
    }
    s.mk_hypothesis(r.get_new(), new_h_proof);
    s.del_hypothesis(hidx);
    return action_result::new_branch();
}

void initialize_unit_preprocess() {
    g_simplify_unit_simp_namespace = new name{"simplifier", "unit_simp"};
    g_simplify_contextual = new name{"simplify", "contextual"};
}

void finalize_unit_preprocess() {
    delete g_simplify_contextual;
    delete g_simplify_unit_simp_namespace;
}

}}
