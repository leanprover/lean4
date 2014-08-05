/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/for_each_fn.h"
#include "library/kernel_bindings.h"
#include "library/locals.h"
#include "library/match.h"

namespace lean {
static name g_tmp_prefix = name::mk_internal_unique_name();

level mk_idx_meta_univ(unsigned i) {
    return mk_meta_univ(name(g_tmp_prefix, i));
}

bool is_idx_meta_univ(level const & l) {
    if (!is_meta(l))
        return false;
    name const & n = meta_id(l);
    return !n.is_atomic() && n.is_numeral() && n.get_prefix() == g_tmp_prefix;
}

unsigned to_meta_idx(level const & l) {
    lean_assert(is_idx_meta_univ(l));
    return meta_id(l).get_numeral();
}

class match_fn : public match_context {
    buffer<optional<expr>> &   m_esubst;
    buffer<optional<level>> &  m_lsubst;
    name_generator             m_ngen;
    name_map<name> *           m_name_subst;
    match_plugin const *       m_plugin;

    void _assign(expr const & p, expr const & t) {
        lean_assert(var_idx(p) < m_esubst.size());
        unsigned vidx = var_idx(p);
        unsigned sz   = m_esubst.size();
        m_esubst[sz - vidx - 1] = t;
    }

    void _assign(level const & p, level const & l) {
        lean_assert(to_meta_idx(p) < m_lsubst.size());
        m_lsubst[to_meta_idx(p)] = l;
    }

    void throw_exception() const {
        throw exception("ill-formed higher-order matching problem");
    }

    optional<expr> _get_subst(expr const & x) const {
        unsigned vidx = var_idx(x);
        unsigned sz = m_esubst.size();
        if (vidx >= sz)
            throw_exception();
        return m_esubst[sz - vidx - 1];
    }

    optional<level> _get_subst(level const & x) const {
        unsigned i = to_meta_idx(x);
        if (i > m_lsubst.size())
            throw_exception();
        return m_lsubst[i];
    }

    virtual void assign(expr const & p, expr const & t) { return _assign(p, t); }
    virtual void assign(level const & p, level const & t) { return _assign(p, t); }
    virtual optional<expr> get_subst(expr const & x) const { return _get_subst(x); }
    virtual optional<level> get_subst(level const & x) const { return _get_subst(x); }
    virtual name mk_name() { return m_ngen.next(); }

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

    bool try_plugin(expr const & p, expr const & t) {
        if (!m_plugin)
            return false;
        return (*m_plugin)(p, t, *this);
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
            if (!_match(p_d, t_d))
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
        return _match(p, t);
    }

    bool match_macro(expr const & p, expr const & t) {
        if (macro_def(p) == macro_def(t) && macro_num_args(p) == macro_num_args(t)) {
            for (unsigned i = 0; i < macro_num_args(p); i++) {
                if (!_match(macro_arg(p, i), macro_arg(t, i)))
                    return false;
            }
            return true;
        }
        return false;
    }

    bool match_app(expr const & p, expr const & t) {
        return match_core(app_fn(p), app_fn(t)) && _match(app_arg(p), app_arg(t));
    }

    bool match_level_core(level const & p, level const & l) {
        if (p == l)
            return true;
        if (p.kind() == l.kind()) {
            switch (p.kind()) {
            case level_kind::Zero:
                lean_unreachable(); // LCOV_EXCL_LINE
            case level_kind::Param: case level_kind::Global: case level_kind::Meta:
                return false;
            case level_kind::Succ:
                return match_level(succ_of(p), succ_of(l));
            case level_kind::Max:
                return
                    match_level(max_lhs(p), max_lhs(l)) &&
                    match_level(max_rhs(p), max_rhs(l));
            case level_kind::IMax:
                return
                    match_level(imax_lhs(p), imax_lhs(l)) &&
                    match_level(imax_rhs(p), imax_rhs(l));
            }
        }
        return false;
    }

    bool match_level(level const & p, level const & l) {
        if (is_idx_meta_univ(p)) {
            auto s = _get_subst(p);
            if (s) {
                return match_level_core(*s, l);
            } else {
                _assign(p, l);
                return true;
            }
        }
        return match_level_core(p, l);
    }

    bool match_levels(levels ps, levels ls) {
        while (ps && ls) {
            if (!match_level(head(ps), head(ls)))
                return false;
            ps = tail(ps);
            ls = tail(ls);
        }
        return true;
    }

    bool match_core(expr const & p, expr const & t) {
        if (p.kind() != t.kind())
            return try_plugin(p, t);
        switch (p.kind()) {
        case expr_kind::Local: case expr_kind::Meta:
            return mlocal_name(p) == mlocal_name(t);
        case expr_kind::Var:
            lean_unreachable(); // LCOV_EXCL_LINE
        case expr_kind::Constant:
            return const_name(p) == const_name(t) && match_levels(const_levels(p), const_levels(t));
        case expr_kind::Sort:
            return match_level(sort_level(p), sort_level(t));
        case expr_kind::Lambda: case expr_kind::Pi:
            return match_binding(p, t) || try_plugin(p, t);
        case expr_kind::Macro:
            return match_macro(p, t) || try_plugin(p, t);
        case expr_kind::App:
            return match_app(p, t) || try_plugin(p, t);
        }
        lean_unreachable(); // LCOV_EXCL_LINE
    }

    bool _match(expr const & p, expr const & t) {
        if (is_var(p)) {
            auto s = _get_subst(p);
            if (s) {
                return match_core(*s, t);
            } else if (has_local(t)) {
                return false;
            } else {
                _assign(p, t);
                return true;
            }
        } else if (is_app(p)) {
            buffer<expr> args;
            expr const & f = get_app_rev_args(p, args);
            if (is_var(f)) {
                // higher-order pattern case
                auto s = _get_subst(f);
                if (s) {
                    expr new_p = apply_beta(*s, args.size(), args.data());
                    return match_core(new_p, t);
                }
                if (args_are_distinct_locals(args)) {
                    optional<expr> new_t = proj(t, args);
                    if (new_t) {
                        _assign(f, *new_t);
                        return true;
                    }
                }
            }
            // fallback to the first-order case
        }

        return match_core(p, t);
    }

public:
    match_fn(buffer<optional<expr>> & esubst, buffer<optional<level>> & lsubst, name_generator const & ngen,
             name_map<name> * name_subst, match_plugin const * plugin):
        m_esubst(esubst), m_lsubst(lsubst), m_ngen(ngen), m_name_subst(name_subst), m_plugin(plugin) {}

    virtual bool match(expr const & p, expr const & t) { return _match(p, t); }
};

bool match(expr const & p, expr const & t, buffer<optional<expr>> & esubst, buffer<optional<level>> & lsubst,
           name const * prefix, name_map<name> * name_subst, match_plugin const * plugin) {
    lean_assert(closed(t));
    if (prefix)
        return match_fn(esubst, lsubst, name_generator(*prefix), name_subst, plugin).match(p, t);
    else
        return match_fn(esubst, lsubst, name_generator(g_tmp_prefix), name_subst, plugin).match(p, t);
}

static unsigned updt_idx_meta_univ_range(level const & l, unsigned r) {
    for_each(l, [&](level const & l) {
            if (!has_meta(l)) return false;
            if (is_idx_meta_univ(l)) {
                unsigned new_r = to_meta_idx(l) + 1;
                if (new_r > r)
                    r = new_r;
            }
            return true;
        });
    return r;
}

static unsigned get_idx_meta_univ_range(expr const & e) {
    if (!has_univ_metavar(e))
        return 0;
    unsigned r = 0;
    for_each(e, [&](expr const & e, unsigned) {
            if (!has_univ_metavar(e)) return false;
            if (is_constant(e))
                for (level const & l : const_levels(e))
                    r = updt_idx_meta_univ_range(l, r);
            if (is_sort(e))
                r = updt_idx_meta_univ_range(sort_level(e), r);
            return true;
        });
    return r;
}

static int match(lua_State * L) {
    expr p     = to_expr(L, 1);
    expr t     = to_expr(L, 2);
    if (!closed(t))
        throw exception("higher-order pattern matching failure, input term must not contain free variables");
    unsigned r1 = get_free_var_range(p);
    unsigned r2 = get_idx_meta_univ_range(p);
    buffer<optional<expr>>  esubst;
    buffer<optional<level>> lsubst;
    esubst.resize(r1); lsubst.resize(r2);
    if (match(p, t, esubst, lsubst, nullptr, nullptr, nullptr)) {
        lua_newtable(L);
        int i = 1;
        for (auto s : esubst) {
            if (s)
                push_expr(L, *s);
            else
                lua_pushboolean(L, false);
            lua_rawseti(L, -2, i);
            i = i + 1;
        }
        lua_newtable(L);
        i = 1;
        for (auto s : lsubst) {
            if (s)
                push_level(L, *s);
            else
                lua_pushboolean(L, false);
            lua_rawseti(L, -2, i);
            i = i + 1;
        }
    } else {
        lua_pushnil(L);
        lua_pushnil(L);
    }
    return 2;
}

static int mk_idx_meta_univ(lua_State * L) {
    return push_level(L, mk_idx_meta_univ(luaL_checkinteger(L, 1)));
}

void open_match(lua_State * L) {
    SET_GLOBAL_FUN(mk_idx_meta_univ, "mk_idx_meta_univ");
    SET_GLOBAL_FUN(match,            "match");
}
}
