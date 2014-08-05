/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "library/kernel_bindings.h"
#include "library/locals.h"
#include "library/match.h"

namespace lean {
class match_fn {
    buffer<optional<expr>> &   m_subst;
    name_generator             m_ngen;
    name_map<name> *           m_name_subst;
    matcher_plugin const * m_plugin;

    void assign(expr const & p, expr const & t) {
        lean_assert(var_idx(p) < m_subst.size());
        unsigned vidx = var_idx(p);
        unsigned sz   = m_subst.size();
        m_subst[sz - vidx - 1] = t;
    }

    optional<expr> get_subst(expr const & x) const {
        unsigned vidx = var_idx(x);
        unsigned sz = m_subst.size();
        if (vidx >= sz)
            throw exception("ill-formed higher-order matching problem");
        return m_subst[sz - vidx - 1];
    }

    bool args_are_distinct_locals(buffer<expr> const & args) {
        for (auto it = args.begin(); it != args.end(); it++) {
            if (!is_local(*it) || contains_local(*it, args.begin(), it))
                return false;
        }
        return true;
    }

    optional<expr> proj(expr const & t, buffer<expr> const & args) {
        expr r = Fun(args, t);
        if (has_local(r))
            return none_expr();
        else
            return some_expr(r);
    }

    bool match_plugin(expr const & p, expr const & t) {
        if (!m_plugin)
            return false;
        return (*m_plugin)(p, t, m_subst, m_ngen.mk_child());
    }

    bool match_binding(expr p, expr t) {
        lean_assert(is_binding(p) && is_binding(t));
        buffer<expr>  ls;
        expr_kind k = p.kind();
        while (p.kind() == k && t.kind() == k) {
            if (m_name_subst)
                (*m_name_subst)[binding_name(p)] = binding_name(t);
            expr p_d  = instantiate_rev(binding_domain(p), ls.size(), ls.data());
            expr t_d  = instantiate_rev(binding_domain(t), ls.size(), ls.data());
            if (!match(p_d, t_d))
                return false;
            expr l  = mk_local(m_ngen.next(), binding_name(t), t_d, binding_info(t));
            ls.push_back(l);
            p = binding_body(p);
            t = binding_body(t);
        }
        if (p.kind() == k || t.kind() == k)
            return false;
        p = instantiate_rev(p, ls.size(), ls.data());
        t = instantiate_rev(t, ls.size(), ls.data());
        return match(p, t);
    }

    bool match_macro(expr const & p, expr const & t) {
        if (macro_def(p) == macro_def(t) && macro_num_args(p) == macro_num_args(t)) {
            for (unsigned i = 0; i < macro_num_args(p); i++) {
                if (!match(macro_arg(p, i), macro_arg(t, i)))
                    return false;
            }
            return true;
        }
        return false;
    }

    bool match_app(expr const & p, expr const & t) {
        return match_core(app_fn(p), app_fn(t)) && match(app_arg(p), app_arg(t));
    }

    bool match_core(expr const & p, expr const & t) {
        if (p.kind() != t.kind())
            return match_plugin(p, t);
        switch (p.kind()) {
        case expr_kind::Local: case expr_kind::Meta:
            return mlocal_name(p) == mlocal_name(t);
        case expr_kind::Var:
            lean_unreachable(); // LCOV_EXCL_LINE
        case expr_kind::Constant:
            // TODO(Leo): universe levels
            return const_name(p) == const_name(t);
        case expr_kind::Sort:
            // TODO(Leo): universe levels
            return true;
        case expr_kind::Lambda: case expr_kind::Pi:
            return match_binding(p, t) || match_plugin(p, t);
        case expr_kind::Macro:
            return match_macro(p, t) || match_plugin(p, t);
        case expr_kind::App:
            return match_app(p, t) || match_plugin(p, t);
        }
        lean_unreachable(); // LCOV_EXCL_LINE
    }

public:
    match_fn(buffer<optional<expr>> & subst, name_generator const & ngen, name_map<name> * name_subst, matcher_plugin const * plugin):
        m_subst(subst), m_ngen(ngen), m_name_subst(name_subst), m_plugin(plugin) {}

    bool match(expr const & p, expr const & t) {
        if (is_var(p)) {
            auto s = get_subst(p);
            if (s) {
                return match_core(*s, t);
            } else if (has_local(t)) {
                return false;
            } else {
                assign(p, t);
                return true;
            }
        } else if (is_app(p)) {
            buffer<expr> args;
            expr const & f = get_app_rev_args(p, args);
            if (is_var(f)) {
                // higher-order pattern case
                auto s = get_subst(f);
                if (s) {
                    expr new_p = apply_beta(*s, args.size(), args.data());
                    return match_core(new_p, t);
                }
                if (args_are_distinct_locals(args)) {
                    optional<expr> new_t = proj(t, args);
                    if (new_t) {
                        assign(f, *new_t);
                        return true;
                    }
                }
            }
            // fallback to the first-order case
        }

        return match_core(p, t);
    }
};

static name g_tmp_prefix = name::mk_internal_unique_name();
bool match(expr const & p, expr const & t, buffer<optional<expr>> & subst, name const * prefix,
               name_map<name> * name_subst, matcher_plugin const * plugin) {
    lean_assert(closed(t));
    if (prefix)
        return match_fn(subst, name_generator(*prefix), name_subst, plugin).match(p, t);
    else
        return match_fn(subst, name_generator(g_tmp_prefix), name_subst, plugin).match(p, t);
}

static int match(lua_State * L) {
    expr p     = to_expr(L, 1);
    expr t     = to_expr(L, 2);
    if (!closed(t))
        throw exception("higher-order pattern matching failure, input term must not contain free variables");
    unsigned k = get_free_var_range(p);
    buffer<optional<expr>> subst;
    subst.resize(k);
    if (match(p, t, subst, nullptr, nullptr, nullptr)) {
        lua_newtable(L);
        int i = 1;
        for (auto s : subst) {
            if (s)
                push_expr(L, *s);
            else
                lua_pushboolean(L, false);
            lua_rawseti(L, -2, i);
            i = i + 1;
        }
    } else {
        lua_pushnil(L);
    }
    return 1;
}

void open_match(lua_State * L) {
    SET_GLOBAL_FUN(match, "match");
}
}
