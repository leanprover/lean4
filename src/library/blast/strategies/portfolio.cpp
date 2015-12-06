/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "library/blast/actions/assert_cc_action.h"
#include "library/blast/simplifier/simplifier_strategies.h"
#include "library/blast/strategies/simple_strategy.h"
#include "library/blast/strategies/preprocess_strategy.h"
#include "library/blast/strategies/debug_action_strategy.h"

namespace lean {
namespace blast {
static optional<expr> apply_preprocess() {
    return preprocess_and_then([]() { return none_expr(); })();
}

static optional<expr> apply_simp() {
    return mk_simplify_using_hypotheses_strategy()();
}

static optional<expr> apply_simp_nohyps() {
    return mk_simplify_all_strategy()();
}

static optional<expr> apply_simple() {
    return preprocess_and_then(mk_simple_strategy())();
}

static optional<expr> apply_cc() {
    return mk_debug_pre_action_strategy(assert_cc_action)();
}

optional<expr> apply_strategy() {
    std::string s_name(get_config().m_strategy);
    if (s_name == "preprocess") {
        return apply_preprocess();
    } else if (s_name == "simp") {
        return apply_simp();
    } else if (s_name == "simp_nohyps") {
        return apply_simp_nohyps();
    } else if (s_name == "simple") {
        return apply_simple();
    } else if (s_name == "cc") {
        return apply_cc();
    } else {
        // TODO(Leo): add more builtin strategies
        return apply_simple();
    }
}
}}
