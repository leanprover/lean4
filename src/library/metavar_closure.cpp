/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/for_each_fn.h"
#include "library/metavar_closure.h"

namespace lean {
void metavar_closure::add(level const & l) {
    for_each(l, [&](level const & l) {
            if (is_meta(l)) {
                m_lvl_mvars.insert(l);
                return false;
            } else {
                return has_meta(l);
            }
        });
}

void metavar_closure::add(expr const & e) {
    for_each(e, [&](expr const & e, unsigned) {
            if (is_metavar(e)) {
                m_expr_mvars.insert(e);
                return false; /* do not visit its type */
            } else if (is_sort(e)) {
                add(sort_level(e));
                return false;
            } else if (is_constant(e)) {
                for (level const & l : const_levels(e))
                    add(l);
                return false;
            } else {
                return has_metavar(e);
            }
        });
}

void metavar_closure::for_each_expr_mvar(std::function<void(expr const &)> const & fn) const {
    m_expr_mvars.for_each(fn);
}

void metavar_closure::for_each_level_mvar(std::function<void(level const &)> const & fn) const {
    m_lvl_mvars.for_each(fn);
}

void metavar_closure::mk_constraints(substitution s, justification const & j, buffer<constraint> & r) const {
    m_expr_mvars.for_each([&](expr const & m) {
            if (s.is_expr_assigned(mlocal_name(m)))
                r.push_back(mk_eq_cnstr(m, s.instantiate(m), j));
        });
    m_lvl_mvars.for_each([&](level const & m) {
            if (s.is_level_assigned(meta_id(m)))
                r.push_back(mk_level_eq_cnstr(m, s.instantiate(m), j));
        });
}

constraints metavar_closure::mk_constraints(substitution s, justification const & j) const {
    buffer<constraint> cs;
    mk_constraints(s, j, cs);
    return to_list(cs.begin(), cs.end());
}
}
