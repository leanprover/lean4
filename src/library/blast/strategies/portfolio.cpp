/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/sstream.h"
#include "library/blast/strategy.h"
#include "library/blast/actions/simple_actions.h"
#include "library/blast/actions/assert_cc_action.h"
#include "library/blast/actions/no_confusion_action.h"
#include "library/blast/unit/unit_actions.h"
#include "library/blast/forward/ematch.h"
#include "library/blast/simplifier/simplifier_strategies.h"
#include "library/blast/recursor/recursor_strategy.h"
#include "library/blast/backward/backward_action.h"
#include "library/blast/backward/backward_strategy.h"
#include "library/blast/grinder/grinder_strategy.h"
#include "library/blast/strategies/simple_strategy.h"
#include "library/blast/strategies/preprocess_strategy.h"
#include "library/blast/strategies/action_strategy.h"

namespace lean {
namespace blast {
static optional<expr> apply_preprocess() {
    return preprocess_and_then(fail_strategy())();
}

static optional<expr> apply_simp() {
    flet<bool> set(get_config().m_simp, true);
    return mk_simplify_using_hypotheses_strategy()();
}

static optional<expr> apply_simp_nohyps() {
    flet<bool> set(get_config().m_simp, true);
    return mk_simplify_all_strategy()();
}

static optional<expr> apply_simple() {
    return preprocess_and_then(mk_simple_strategy())();
}

static optional<expr> apply_cc() {
    flet<bool> set(get_config().m_cc, true);
    return mk_pre_action_strategy("cc",
                                  [](hypothesis_idx hidx) {
                                      Try(no_confusion_action(hidx));
                                      Try(assert_cc_action(hidx));
                                      return action_result::new_branch();
                                  })();
}

static optional<expr> apply_ematch() {
    flet<bool> set(get_config().m_ematch, true);
    return mk_action_strategy("ematch",
                              assert_cc_action,
                              unit_propagate,
                              ematch_action)();
}

static optional<expr> apply_ematch_simp() {
    flet<bool> set(get_config().m_ematch, true);
    return mk_action_strategy("ematch_simp",
                              [](hypothesis_idx hidx) {
                                  Try(no_confusion_action(hidx));
                                  TrySolve(assert_cc_action(hidx));
                                  return action_result::new_branch();
                              },
                              unit_propagate,
                              ematch_simp_action)();
}

static optional<expr> apply_rec_simp() {
    return rec_and_then(apply_simp)();
}

static optional<expr> apply_rec_ematch_simp() {
    return rec_and_then(apply_ematch_simp)();
}

static optional<expr> apply_constructor() {
    return mk_action_strategy("constructor",
                              []() { return constructor_action(); })();
}

static optional<expr> apply_backward() {
    return preprocess_and_then(mk_backward_strategy())();
}

static optional<expr> apply_unit() {
    return mk_action_strategy("unit",
                              unit_preprocess,
                              unit_propagate,
                              fail_action)();
}

static optional<expr> apply_core_grind() {
    return grind_and_then(fail_strategy())();
}

static optional<expr> apply_grind() {
    return preprocess_and_then(grind_and_then(mk_backward_strategy("grind_back")))();
}

static optional<expr> apply_grind_simp() {
    strategy main = mk_xbackward_strategy("grind_simp",
                                          fail_action_h, fail_action_h, fail_action,
                                          []() { TryStrategy(apply_simp); return action_result::failed(); });
    return preprocess_and_then(grind_and_then(main))();
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
    } else if (s_name == "all") {
        // TODO(Leo):
        return apply_simple();
    } else if (s_name == "cc") {
        return apply_cc();
    } else if (s_name == "grind") {
        return apply_grind();
    } else if (s_name == "grind_simp") {
        return apply_grind_simp();
    } else if (s_name == "core_grind") {
        return apply_core_grind();
    } else if (s_name == "ematch") {
        return apply_ematch();
    } else if (s_name == "ematch_simp") {
        return apply_ematch_simp();
    } else if (s_name == "rec_ematch_simp") {
        return apply_rec_ematch_simp();
    } else if (s_name == "rec_simp") {
        return apply_rec_simp();
    } else if (s_name == "constructor") {
        return apply_constructor();
    } else if (s_name == "unit") {
        return apply_unit();
    } else if (s_name == "backward") {
        return apply_backward();
    } else {
        throw exception(sstream() << "unknown blast strategy '" << s_name << "'");
    }
}
}}
