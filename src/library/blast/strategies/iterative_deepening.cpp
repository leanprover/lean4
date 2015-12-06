/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/blast/strategy.h"
#include "library/blast/choice_point.h"
#include "library/blast/options.h"

namespace lean {
namespace blast {
strategy iterative_deepening(strategy const & S, unsigned init, unsigned inc, unsigned max) {
    return [=]() { // NOLINT
        state s      = curr_state();
        unsigned ncs = get_num_choice_points();
        unsigned d   = init;
        while (true) {
            flet<unsigned> set_depth(get_config().m_max_depth, d);
            if (auto r = S())
                return r;
            d += inc;
            if (d > max) {
                if (get_config().m_show_failure)
                    display_curr_state();
                return none_expr();
            }
            curr_state() = s;
            shrink_choice_points(ncs);
        };
    };
}
}}
