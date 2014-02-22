/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include "kernel/metavar.h"

namespace lean {
bool substitution::is_assigned(name const & m) const {
    return m_subst.contains(m);
}

optional<std::pair<expr, justification>> substitution::get_assignment(name const & m) const {
    auto it = m_subst.find(m);
    if (it)
        return optional<std::pair<expr, justification>>(*it);
    else
        return optional<std::pair<expr, justification>>();
}

optional<expr> substitution::get_expr(name const & m) const {
    auto it = m_subst.find(m);
    if (it)
        return some_expr(it->first);
    else
        return none_expr();
}

void substitution::assign(name const & m, expr const & t, justification const & j) {
    m_subst.insert(m, mk_pair(t, j));
}

void substitution::assign(name const & m, expr const & t) {
    assign(m, t, justification());
}

void substitution::for_each(std::function<void(name const & n, expr const & e, justification const & j)> const & fn) {
    m_subst.for_each([=](name const & n, std::pair<expr, justification> const & a) {
            fn(n, a.first, a.second);
        });
}
}
