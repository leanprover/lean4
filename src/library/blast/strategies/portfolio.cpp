/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/blast/strategies/simple_strategy.h"
#include "library/blast/strategies/preprocess_strategy.h"

namespace lean {
namespace blast {
static optional<expr> apply_simple() {
    return preprocess_and_then(mk_simple_strategy())();
}

optional<expr> apply_strategy() {
    return apply_simple();
}
}}
