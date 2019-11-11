/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "runtime/interrupt.h"
#include "kernel/for_each_fn.h"
#include "library/idx_metavar.h"
#include "library/metavar_context.h"
#include "library/replace_visitor.h"

#ifndef LEAN_INSTANTIATE_METAIDX_CACHE_CAPACITY
#define LEAN_INSTANTIATE_METAIDX_CACHE_CAPACITY 1024*8
#endif

namespace lean {
static name * g_tmp_prefix = nullptr;

void initialize_idx_metavar() {
    g_tmp_prefix = new name(name::mk_internal_unique_name());
}

void finalize_idx_metavar() {
    delete g_tmp_prefix;
}

level mk_idx_metauniv(unsigned i) {
    return mk_univ_mvar(name(*g_tmp_prefix, i));
}

expr mk_idx_metavar(unsigned i, expr const & type) {
    return mk_metavar(name(*g_tmp_prefix, i), type);
}

bool is_idx_metauniv(level const & l) {
    if (!is_mvar(l))
        return false;
    name const & n = mvar_id(l);
    return !n.is_atomic() && n.is_numeral() && n.get_prefix() == *g_tmp_prefix;
}

unsigned to_meta_idx(level const & l) {
    lean_assert(is_idx_metauniv(l));
    return mvar_id(l).get_numeral().get_small_value();
}

bool is_idx_metavar(expr const & e) {
    if (!is_metavar(e))
        return false;
    name const & n = mvar_name(e);
    return !n.is_atomic() && n.is_numeral() && n.get_prefix() == *g_tmp_prefix;
}

unsigned to_meta_idx(expr const & e) {
    lean_assert(is_idx_metavar(e));
    return mvar_name(e).get_numeral().get_small_value();
}

bool has_idx_metauniv(level const & l) {
    if (!has_mvar(l))
        return false;
    bool found = false;
    for_each(l, [&](level const & l) {
            if (found) return false;
            if (!has_mvar(l)) return false;
            if (is_idx_metauniv(l))
                found = true;
            return true;
        });
    return found;
}

bool has_idx_metavar(expr const & e) {
    if (!has_univ_metavar(e) && !has_expr_metavar(e))
        return false;
    bool found = false;
    for_each(e, [&](expr const & e, unsigned) {
            if (found) return false;
            if (!has_univ_metavar(e) && !has_expr_metavar(e)) return false;
            if (is_idx_metavar(e))
                found = true;
            else if (is_constant(e) && std::any_of(const_levels(e).begin(), const_levels(e).end(), has_idx_metauniv))
                found = true;
            else if (is_sort(e) && has_idx_metauniv(sort_level(e)))
                found = true;
            return true;
        });
    return found;
}

bool has_idx_expr_metavar(expr const & e) {
    if (!has_expr_metavar(e))
        return false;
    bool found = false;
    for_each(e, [&](expr const & e, unsigned) {
            if (found || !has_expr_metavar(e)) return false;
            if (is_idx_metavar(e)) found = true;
            return true;
        });
    return found;
}

struct to_idx_metavars_fn : public replace_visitor {
    metavar_context const & m_mctx;
    buffer<level> &         m_new_us;
    buffer<expr> &          m_new_ms;
    name_map<level>         m_lvl_cache;

    to_idx_metavars_fn(metavar_context const & mctx, buffer<level> & new_us, buffer<expr> & new_ms):
        m_mctx(mctx), m_new_us(new_us), m_new_ms(new_ms) {}

    level visit(level const & l) {
        if (!has_mvar(l)) return l;
        return replace(l, [&](level const & l) {
                if (is_mvar(l) && !is_idx_metauniv(l)) {
                    if (auto it = m_lvl_cache.find(mvar_id(l)))
                        return some_level(*it);
                    level new_l = mk_idx_metauniv(m_new_us.size());
                    m_lvl_cache.insert(mvar_id(l), new_l);
                    m_new_us.push_back(new_l);
                    return some_level(new_l);
                }
                return none_level();
            });
    }

    levels visit(levels const & ls) {
        return map_reuse(ls, [&](level const & l) { return visit(l); });
    }

    virtual expr visit_meta(expr const & m) override {
        if (is_idx_metavar(m)) {
            return m;
        } else if (auto decl = m_mctx.find_metavar_decl(m)) {
            expr new_type = visit(decl->get_type());
            unsigned i    = m_new_ms.size();
            expr new_m    = mk_idx_metavar(i, new_type);
            m_new_ms.push_back(new_m);
            return new_m;
        } else {
            throw exception("unexpected occurrence of metavariable");
        }
    }

    virtual expr visit_constant(expr const & e) override {
        return update_constant(e, visit(const_levels(e)));
    }

    virtual expr visit_sort(expr const & e) override {
        return update_sort(e, visit(sort_level(e)));
    }

    virtual expr visit(expr const & e) override {
        if (!has_metavar(e)) return e;
        return replace_visitor::visit(e);
    }
};

expr to_idx_metavars(metavar_context const & mctx, expr const & e, buffer<level> & new_us, buffer<expr> & new_ms) {
    if (!has_metavar(e))
        return e;
    return to_idx_metavars_fn(mctx, new_us, new_ms)(e);
}
}
