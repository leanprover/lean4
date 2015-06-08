/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <utility>
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/for_each_fn.h"
#include "kernel/type_checker.h"
#include "library/kernel_bindings.h"
#include "library/locals.h"
#include "library/match.h"
#include "library/idx_metavar.h"

namespace lean {
class match_fn : public match_context {
    unsigned                          m_esubst_sz;
    optional<expr> *                  m_esubst;
    unsigned                          m_lsubst_sz;
    optional<level> *                 m_lsubst;
    name_generator                    m_ngen;
    name_map<name> *                  m_name_subst;
    match_plugin const *              m_plugin;
    buffer<pair<bool, unsigned>>      m_stack;
    buffer<unsigned>                  m_scopes;
    bool *                            m_assigned; // mark if matcher assigned anything
    void push() {
        m_scopes.push_back(m_stack.size());
    }

    void pop() {
        lean_assert(!m_scopes.empty());
        unsigned old_sz = m_scopes.back();
        while (m_stack.size() > old_sz) {
            auto p = m_stack.back();
            if (p.first)
                m_esubst[p.second] = none_expr();
            else
                m_lsubst[p.second] = none_level();
            m_stack.pop_back();
        }
        m_scopes.pop_back();
    }

    void keep() {
        m_scopes.back() = m_stack.size();
    }

    struct scope {
        match_fn & m;
        scope(match_fn & _m):m(_m) { m.push(); }
        ~scope() { m.pop(); }
        void keep() { m.keep(); }
    };

    void _assign(expr const & p, expr const & t) {
        lean_assert(to_meta_idx(p) < m_esubst_sz);
        unsigned i  = to_meta_idx(p);
        m_stack.emplace_back(true, i);
        m_esubst[i] = t;
        if (m_assigned)
            *m_assigned = true;
    }

    void _assign(level const & p, level const & l) {
        lean_assert(to_meta_idx(p) < m_lsubst_sz);
        unsigned i = to_meta_idx(p);
        m_stack.emplace_back(false, i);
        m_lsubst[i] = l;
        if (m_assigned)
            *m_assigned = true;
    }

    void throw_exception() const {
        throw exception("ill-formed higher-order matching problem");
    }

    optional<expr> _get_subst(expr const & x) const {
        unsigned i  = to_meta_idx(x);
        unsigned sz = m_esubst_sz;
        if (i >= sz)
            throw_exception();
        return m_esubst[i];
    }

    optional<level> _get_subst(level const & x) const {
        unsigned i = to_meta_idx(x);
        if (i >= m_lsubst_sz)
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
        return m_plugin->on_failure(p, t, *this);
    }

    bool match_binding_core(expr p, expr t) {
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
        p = instantiate_rev(p, ls.size(), ls.data());
        t = instantiate_rev(t, ls.size(), ls.data());
        return _match(p, t);
    }

    bool match_binding(expr const & p, expr const & t) {
        {
            scope s(*this);
            if (match_binding_core(p, t)) {
                s.keep();
                return true;
            }
        }
        return try_plugin(p, t);
    }

    bool match_macro_core(expr const & p, expr const & t) {
        if (macro_def(p) == macro_def(t) && macro_num_args(p) == macro_num_args(t)) {
            for (unsigned i = 0; i < macro_num_args(p); i++) {
                if (!_match(macro_arg(p, i), macro_arg(t, i)))
                    return false;
            }
            return true;
        }
        return false;
    }

    bool match_macro(expr const & p, expr const & t) {
        {
            scope s(*this);
            if (match_macro_core(p, t)) {
                s.keep();
                return true;
            }
        }
        return try_plugin(p, t);
    }

    bool match_app_core(expr const & p, expr const & t) {
        buffer<expr> p_args;
        buffer<expr> t_args;
        expr const & p_fn = get_app_args(p, p_args);
        expr const & t_fn = get_app_args(t, t_args);
        if (p_args.size() != t_args.size())
            return false;
        if (!match_core(p_fn, t_fn))
            return false;
        for (unsigned i = 0; i < p_args.size(); i++) {
            if (!_match(p_args[i], t_args[i]))
                return false;
        }
        return true;
    }

    bool match_app(expr const & p, expr const & t) {
        {
            scope s(*this);
            if (match_app_core(p, t)) {
                s.keep();
                return true;
            }
        }
        return try_plugin(p, t);
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
            case level_kind::Max: {
                scope s(*this);
                if (match_level(max_lhs(p), max_lhs(l)) && match_level(max_rhs(p), max_rhs(l))) {
                    s.keep();
                    return true;
                }
                break;
            }
            case level_kind::IMax: {
                scope s(*this);
                if (match_level(imax_lhs(p), imax_lhs(l)) && match_level(imax_rhs(p), imax_rhs(l))) {
                    s.keep();
                    return true;
                }
                break;
            }}
        }
        level p1 = normalize(p);
        level l1 = normalize(l);
        if (p1 != p || l1 != l)
            return match_level(p1, l1);
        else
            return false;
    }

    bool match_level(level const & p, level const & l) {
        if (is_idx_metauniv(p)) {
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

    bool match_constant(expr const & p, expr const & t) {
        if (const_name(p) == const_name(t))
            return match_levels(const_levels(p), const_levels(t));
        else
            return try_plugin(p, t);
    }

    static expr eta(expr const & e) {
        unsigned num = 0;
        expr it = e;
        while (is_lambda(it)) {
            num++;
            it = binding_body(it);
        }
        if (num == 0)
            return e;
        for (unsigned i = 0; i < num; i++) {
            if (!is_app(it))
                return e;
            if (!is_var(app_arg(it), i)) {
                return e;
            }
            it = app_fn(it);
        }
        if (!closed(it))
            return e;
        return it;
    }

    bool match_core(expr const & p, expr const & t) {
        if (p.kind() != t.kind()) {
            if (is_lambda(p) != is_lambda(t)) {
                expr new_p = eta(p);
                expr new_t = eta(t);
                if (is_lambda(new_p) == is_lambda(new_t))
                    return _match(new_p, new_t);
            }
            return try_plugin(p, t);
        }

        if (m_plugin) {
            switch (m_plugin->pre(p, t, *this)) {
            case l_true:  return true;
            case l_false: return false;
            case l_undef: break;
            }
        }

        switch (p.kind()) {
        case expr_kind::Local: case expr_kind::Meta:
            return mlocal_name(p) == mlocal_name(t);
        case expr_kind::Var:
            lean_unreachable(); // LCOV_EXCL_LINE
        case expr_kind::Constant:
            return match_constant(p, t);
        case expr_kind::Sort:
            return match_level(sort_level(p), sort_level(t));
        case expr_kind::Lambda: case expr_kind::Pi:
            return match_binding(p, t);
        case expr_kind::Macro:
            return match_macro(p, t);
        case expr_kind::App:
            return match_app(p, t);
        }
        lean_unreachable(); // LCOV_EXCL_LINE
    }

    bool _match(expr const & p, expr const & t) {
        if (is_idx_metavar(p)) {
            auto s = _get_subst(p);
            if (s) {
                return match_core(*s, t);
            } else {
                _assign(p, t);
                return true;
            }
        } else if (is_app(p)) {
            buffer<expr> args;
            expr const & f = get_app_rev_args(p, args);
            if (is_idx_metavar(f)) {
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
    match_fn(unsigned lsubst_sz, optional<level> * lsubst,
             unsigned esubst_sz, optional<expr> * esubst,
             name_generator const & ngen,
             name_map<name> * name_subst, match_plugin const * plugin, bool * assigned):
        m_esubst_sz(esubst_sz), m_esubst(esubst),
        m_lsubst_sz(lsubst_sz), m_lsubst(lsubst),
        m_ngen(ngen), m_name_subst(name_subst), m_plugin(plugin),
        m_assigned(assigned) {}

    virtual bool match(expr const & p, expr const & t) { return _match(p, t); }
};

bool match(expr const & p, expr const & t,
           unsigned lsubst_sz, optional<level> * lsubst,
           unsigned esubst_sz, optional<expr> * esubst,
           name const * prefix, name_map<name> * name_subst, match_plugin const * plugin, bool * assigned) {
    lean_assert(closed(t));
    lean_assert(closed(p));
    if (prefix)
        return match_fn(lsubst_sz, lsubst, esubst_sz, esubst, name_generator(*prefix),
                        name_subst, plugin, assigned).match(p, t);
    else
        return match_fn(lsubst_sz, lsubst, esubst_sz, esubst,
                        name_generator(), name_subst, plugin, assigned).match(p, t);
}

bool match(expr const & p, expr const & t, buffer<optional<level>> & lsubst, buffer<optional<expr>> & esubst,
           name const * prefix, name_map<name> * name_subst, match_plugin const * plugin, bool * assigned) {
    return match(p, t, lsubst.size(), lsubst.data(), esubst.size(), esubst.data(),
                 prefix, name_subst, plugin, assigned);
}

bool whnf_match_plugin::on_failure(expr const & p, expr const & t, match_context & ctx) const {
    try {
        constraint_seq cs;
        expr p1 = m_tc.whnf(p, cs);
        expr t1 = m_tc.whnf(t, cs);
        return !cs && (p1 != p || t1 != t) && ctx.match(p1, t1);
    } catch (exception&) {
        return false;
    }
}

static unsigned updt_idx_meta_univ_range(level const & l, unsigned r) {
    for_each(l, [&](level const & l) {
            if (!has_meta(l)) return false;
            if (is_idx_metauniv(l)) {
                unsigned new_r = to_meta_idx(l) + 1;
                if (new_r > r)
                    r = new_r;
            }
            return true;
        });
    return r;
}

static pair<unsigned, unsigned> get_idx_meta_univ_ranges(expr const & e) {
    if (!has_metavar(e))
        return mk_pair(0, 0);
    unsigned rlvl = 0;
    unsigned rexp = 0;
    for_each(e, [&](expr const & e, unsigned) {
            if (!has_metavar(e)) return false;
            if (is_constant(e))
                for (level const & l : const_levels(e))
                    rlvl = updt_idx_meta_univ_range(l, rlvl);
            if (is_sort(e))
                rlvl = updt_idx_meta_univ_range(sort_level(e), rlvl);
            if (is_idx_metavar(e))
                rexp = std::max(to_meta_idx(e) + 1, rexp);
            return true;
        });
    return mk_pair(rlvl, rexp);
}

typedef std::shared_ptr<match_plugin> match_plugin_ref;
DECL_UDATA(match_plugin_ref)

static const struct luaL_Reg match_plugin_ref_m[] = {
    {"__gc", match_plugin_ref_gc},
    {0, 0}
};

// version of whnf_match_plugin for Lua
class whnf_match_plugin2 : public whnf_match_plugin {
    std::shared_ptr<type_checker> m_tc_ref;
public:
    whnf_match_plugin2(std::shared_ptr<type_checker> & tc):
        whnf_match_plugin(*tc), m_tc_ref(tc) {}
};

static int mk_whnf_match_plugin(lua_State * L) {
    return push_match_plugin_ref(L, match_plugin_ref(new whnf_match_plugin2(to_type_checker_ref(L, 1))));
}

static int match(lua_State * L) {
    int nargs  = lua_gettop(L);
    expr p     = to_expr(L, 1);
    expr t     = to_expr(L, 2);
    match_plugin * plugin = nullptr;
    if (nargs >= 3)
        plugin = to_match_plugin_ref(L, 3).get();
    if (!closed(t))
        throw exception("higher-order pattern matching failure, input term must not contain free variables");
    unsigned r1, r2;
    auto r1_r2 = get_idx_meta_univ_ranges(p);
    r1 = r1_r2.first;
    r2 = r1_r2.second;
    buffer<optional<level>> lsubst;
    buffer<optional<expr>>  esubst;
    lsubst.resize(r1); esubst.resize(r2);
    if (match(p, t, lsubst, esubst, nullptr, nullptr, plugin)) {
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

static int mk_idx_metauniv(lua_State * L) {
    return push_level(L, mk_idx_metauniv(luaL_checkinteger(L, 1)));
}

static int mk_idx_metavar(lua_State * L) {
    return push_expr(L, mk_idx_metavar(luaL_checkinteger(L, 1), to_expr(L, 2)));
}

void open_match(lua_State * L) {
    luaL_newmetatable(L, match_plugin_ref_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, match_plugin_ref_m, 0);

    SET_GLOBAL_FUN(mk_whnf_match_plugin,  "whnf_match_plugin");
    SET_GLOBAL_FUN(match_plugin_ref_pred, "is_match_plugin");
    SET_GLOBAL_FUN(mk_idx_metauniv,       "mk_idx_metauniv");
    SET_GLOBAL_FUN(mk_idx_metavar,        "mk_idx_metavar");
    SET_GLOBAL_FUN(match,                 "match");
}
}
