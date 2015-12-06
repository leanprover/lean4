/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "library/blast/strategies/simple_strategy.h"
#include "library/blast/strategies/preprocess_strategy.h"

namespace lean {
namespace blast {
static optional<expr> apply_preprocess() {
    return preprocess_and_then([]() { return none_expr(); })();
}

static optional<expr> apply_simple() {
    return preprocess_and_then(mk_simple_strategy())();
}

optional<expr> apply_strategy() {
    std::string s_name(get_config().m_strategy);
    if (s_name == "preprocess") {
        return apply_preprocess();
    } else if (s_name == "simple") {
        return apply_simple();
    } else {
        // TODO(Leo): add more builtin strategies
        return apply_simple();
    }
}
}}
