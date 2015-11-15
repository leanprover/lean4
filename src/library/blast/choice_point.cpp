/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include "library/blast/blast.h"
#include "library/blast/choice_point.h"

namespace lean {
namespace blast {
MK_THREAD_LOCAL_GET_DEF(std::vector<choice_point>, get_choice_points);

void init_choice_points() {
    get_choice_points().clear();
}

void push_choice_point(choice_point const & c) {
    get_choice_points().push_back(c);
}

action_result next_choice_point(unsigned base) {
    auto & cs = get_choice_points();
    while (true) {
        if (cs.size() == base)
            return action_result::failed();
        action_result r = cs.back().next();
        if (!failed(r))
            return r;
        cs.pop_back();
    }
}

unsigned get_num_choice_points() {
    return get_choice_points().size();
}

void shrink_choice_points(unsigned n) {
    lean_assert(n <= get_choice_points().size());
    get_choice_points().resize(n);
}

void clear_choice_points() {
    get_choice_points().clear();
}
}}
