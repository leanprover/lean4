/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/choice_iterator.h"

namespace lean {
lazy_list<constraints> choose(std::shared_ptr<choice_iterator> c, bool ignore_failure) {
    return mk_lazy_list<constraints>([=]() {
            auto s = c->next();
            if (s) {
                return some(mk_pair(*s, choose(c, false)));
            } else if (ignore_failure) {
                // return singleton empty list of constraints, and let tactic hints try to instantiate the metavariable.
                return lazy_list<constraints>::maybe_pair(constraints(), lazy_list<constraints>());
            } else {
                return lazy_list<constraints>::maybe_pair();
            }
        });
}

lazy_list<constraints> choose(std::shared_ptr<choice_iterator> c) {
    return choose(c, c->ignore_failure());
}
}
