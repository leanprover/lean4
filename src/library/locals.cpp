/*
Copyright (c) 2014-2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/name_set.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/expr.h"
#include "kernel/for_each_fn.h"
#include "kernel/find_fn.h"
#include "library/locals.h"

namespace lean {
void collect_univ_params_core(level const & l, name_set & r) {
    for_each(l, [&](level const & l) {
            if (!has_param(l))
                return false;
            if (is_param(l))
                r.insert(param_id(l));
            return true;
        });
}

name_set collect_univ_params(expr const & e, name_set const & ls) {
    if (!has_param_univ(e)) {
        return ls;
    } else {
        name_set r = ls;
        for_each(e, [&](expr const & e, unsigned) {
                if (!has_param_univ(e)) {
                    return false;
                } else if (is_sort(e)) {
                    collect_univ_params_core(sort_level(e), r);
                } else if (is_constant(e)) {
                    for (auto const & l : const_levels(e))
                        collect_univ_params_core(l, r);
                }
                return true;
            });
        return r;
    }
}

level_param_names to_level_param_names(name_set const & ls) {
    level_param_names r;
    ls.for_each([&](name const & n) {
            r = level_param_names(n, r);
        });
    return r;
}

void collected_locals::insert(expr const & l) {
    if (m_local_names.contains(mlocal_name(l)))
        return;
    m_local_names.insert(mlocal_name(l));
    m_locals.push_back(l);
}

void collect_locals(expr const & e, collected_locals & ls, bool restricted) {
    if (!has_local(e))
        return;
    expr_set visited;
    std::function<void(expr const & e)> visit = [&](expr const & e) {
        if (!has_local(e))
            return;
        if (restricted && is_meta(e))
            return;
        if (visited.find(e) != visited.end())
            return;
        visited.insert(e);
        switch (e.kind()) {
        case expr_kind::Var: case expr_kind::Constant: case expr_kind::Sort:
            break; // do nothing
        case expr_kind::Local:
            if (!restricted)
                visit(mlocal_type(e));
            ls.insert(e);
            break;
        case expr_kind::Meta:
            lean_assert(!restricted);
            visit(mlocal_type(e));
            break;
        case expr_kind::Macro:
            for (unsigned i = 0; i < macro_num_args(e); i++)
                visit(macro_arg(e, i));
            break;
        case expr_kind::App:
            visit(app_fn(e));
            visit(app_arg(e));
            break;
        case expr_kind::Lambda:
        case expr_kind::Pi:
            visit(binding_domain(e));
            visit(binding_body(e));
            break;
        }
    };
    visit(e);
}

bool contains_local(expr const & e, name const & n) {
    if (!has_local(e))
        return false;
    bool result = false;
    for_each(e, [&](expr const & e, unsigned) {
            if (result || !has_local(e))  {
                return false;
            } else if (is_local(e) && mlocal_name(e) == n) {
                result = true;
                return false;
            } else {
                return true;
            }
        });
    return result;
}

optional<expr> depends_on(unsigned sz, expr const * es, expr const & h) {
    for (unsigned i = 0; i < sz; i++)
        if (depends_on(es[i], h))
            return some_expr(es[i]);
    return none_expr();
}

bool depends_on_any(expr const & e, unsigned hs_sz, expr const * hs) {
    return std::any_of(hs, hs+hs_sz, [&](expr const & h) { return depends_on(e, h); });
}

expr replace_locals(expr const & e, unsigned sz, expr const * locals, expr const * terms) {
    return instantiate_rev(abstract_locals(e, sz, locals), sz, terms);
}

expr replace_locals(expr const & e, buffer<expr> const & locals, buffer<expr> const & terms) {
    lean_assert(locals.size() == terms.size());
    lean_assert(std::all_of(locals.begin(), locals.end(), is_local));
    return replace_locals(e, locals.size(), locals.data(), terms.data());
}
}
