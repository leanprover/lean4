/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/scoped_map.h"
#include "util/name_map.h"
#include "kernel/instantiate.h"
#include "library/match.h"
#include "library/app_builder.h"
#include "library/kernel_bindings.h"

namespace lean {

struct app_builder::imp {
    // For each declaration we associate the number of explicit arguments provided to
    // it, and which of them are used to infer the implicit arguments.
    struct decl_info {
        unsigned       m_nargs; // total number of explicit arguments
        list<unsigned> m_used_idxs; // which ones are used to infer implicit arguments
        decl_info(unsigned nargs, list<unsigned> const & used_idxs):
            m_nargs(nargs), m_used_idxs(used_idxs) {}
        decl_info() {}
    };

    struct cache_key {
        name         m_name;
        list<expr>   m_arg_types;
        unsigned     m_hash;
        cache_key(name const & n, unsigned num_arg_types, expr const * arg_types):
            m_name(n), m_arg_types(to_list(arg_types, arg_types + num_arg_types)) {
            m_hash      = m_name.hash();
            for (unsigned i = 0; i < num_arg_types; i++)
                m_hash  = hash(m_hash, arg_types[i].hash());
        }
    };
    struct cache_key_hash_fn {
        unsigned operator()(cache_key const & e) const { return e.m_hash; }
    };
    struct cache_key_equal_fn {
        bool operator()(cache_key const & e1, cache_key const & e2) const {
            return
                e1.m_name == e2.m_name &&
                e1.m_arg_types == e2.m_arg_types;
        }
    };

    // The cache stores a mapping (decl + type of explicit arguments ==> term t).
    // If t is closed term, then we obtain the final application by using
    //       mk_app(t, explicit_args)
    // If t contains free variables, then we obtain the final application by using
    //       instantiate(t, explicit_args)
    typedef scoped_map<cache_key, expr, cache_key_hash_fn, cache_key_equal_fn> cache;

    type_checker &      m_tc;
    whnf_match_plugin   m_plugin;
    name_map<decl_info> m_decl_info;
    cache               m_cache;
    buffer<levels>      m_levels;

    imp(type_checker & tc):m_tc(tc), m_plugin(tc) {
        m_levels.push_back(levels());
    }

    // Make sure m_levels contains at least nlvls metavariable universe levels
    void ensure_levels(unsigned nlvls) {
        while (m_levels.size() <= nlvls) {
            level new_lvl   = mk_idx_metauniv(m_levels.size() - 1);
            levels new_lvls = append(m_levels.back(), levels(new_lvl));
            m_levels.push_back(new_lvls);
        }
    }

    // We say the given mask is simple if it is of the form (false*, true*).
    // That is, a block of false followed by a blocked of true
    static bool is_simple_mask(buffer<bool> & explicit_mask) {
        bool found_true = false;
        for (bool const & b : explicit_mask) {
            if (b)
                found_true = true;
            else if (found_true)
                return false;
        }
        return true;
    }

    void save_decl_info(declaration const & d, unsigned nargs, buffer<unsigned> const & used_idxs) {
        if (!m_decl_info.contains(d.get_name())) {
            m_decl_info.insert(d.get_name(), decl_info(nargs, to_list(used_idxs)));
        }
    }

    optional<expr> mk_app_core(declaration const & d, unsigned nargs, expr const * args, bool use_cache) {
        unsigned num_univs = d.get_num_univ_params();
        ensure_levels(num_univs);
        expr type  = instantiate_type_univ_params(d, m_levels[num_univs]);
        buffer<optional<level>> lsubst;
        buffer<optional<expr>>  esubst;
        lsubst.resize(num_univs, none_level());
        constraint_seq cs;
        buffer<unsigned> used_idxs;
        buffer<expr>     used_types;
        buffer<bool>     explicit_mask;
        buffer<expr> domain_types;
        unsigned idx = 0;
        while (is_pi(type)) {
            explicit_mask.push_back(is_explicit(binding_info(type)));
            esubst.push_back(none_expr());
            domain_types.push_back(binding_domain(type));
            // TODO(Leo): perhaps, we should cache the result of this while-loop.
            // The result of this computation can be reused in future calls.
            expr meta = mk_idx_metavar(idx, binding_domain(type));
            idx++;
            type = instantiate(binding_body(type), meta);
        }
        unsigned i = domain_types.size();
        unsigned j = nargs;
        while (i > 0) {
            --i;
            if (explicit_mask[i]) {
                if (j == 0)
                    return none_expr();
                --j;
                expr arg_type = m_tc.infer(args[j], cs);
                if (cs)
                    return none_expr();
                bool assigned = false;
                if (!match(domain_types[i], arg_type, lsubst, esubst,
                           nullptr, nullptr, &m_plugin, &assigned))
                    return none_expr();
                if (assigned && use_cache) {
                    used_idxs.push_back(j);
                    used_types.push_back(arg_type);
                }
                esubst[i] = some_expr(args[j]);
            } else {
                if (!esubst[i])
                    return none_expr();
                expr arg_type = m_tc.infer(*esubst[i], cs);
                if (cs)
                    return none_expr();
                if (!match(domain_types[i], arg_type, lsubst, esubst,
                           nullptr, nullptr, &m_plugin))
                    return none_expr();
            }
        }
        bool has_unassigned_lvls = std::find(lsubst.begin(), lsubst.end(), none_level()) != lsubst.end();
        if (j > 0 || has_unassigned_lvls)
            return none_expr();
        if (use_cache)
            save_decl_info(d, nargs, used_idxs);
        buffer<level> r_lvls;
        for (optional<level> const & l : lsubst)
            r_lvls.push_back(*l);
        buffer<expr> r_args;
        for (optional<expr> const & o : esubst)
            r_args.push_back(*o);
        lean_assert(explicit_mask.size() == r_args.size());
        if (!use_cache) {
            return some_expr(::lean::mk_app(mk_constant(d.get_name(), to_list(r_lvls)), r_args.size(), r_args.data()));
        } else if (is_simple_mask(explicit_mask)) {
            expr f = ::lean::mk_app(mk_constant(d.get_name(), to_list(r_lvls)), r_args.size() - nargs, r_args.data());
            if (use_cache) {
                cache_key k(d.get_name(), used_types.size(), used_types.data());
                m_cache.insert(k, f);
            }
            return some_expr(::lean::mk_app(f, nargs, r_args.end() - nargs));
        } else {
            buffer<expr> imp_args;
            buffer<expr> expl_args;
            for (unsigned i = 0; i < explicit_mask.size(); i++) {
                if (explicit_mask[i]) {
                    imp_args.push_back(mk_var(expl_args.size()));
                    expl_args.push_back(r_args[i]);
                } else {
                    imp_args.push_back(r_args[i]);
                }
            }
            expr f = ::lean::mk_app(mk_constant(d.get_name(), to_list(r_lvls)), imp_args.size(), imp_args.data());
            if (use_cache) {
                cache_key k(d.get_name(), used_types.size(), used_types.data());
                m_cache.insert(k, f);
            }
            return some_expr(instantiate(f, expl_args.size(), expl_args.data()));
        }
    }

    optional<expr> mk_app(declaration const & d, unsigned nargs, expr const * args, bool use_cache) {
        if (use_cache) {
            if (auto info = m_decl_info.find(d.get_name())) {
                if (info->m_nargs != nargs)
                    return none_expr();
                buffer<expr> arg_types;
                constraint_seq cs;
                for (unsigned idx : info->m_used_idxs) {
                    lean_assert(idx < nargs);
                    expr t = m_tc.infer(args[idx], cs);
                    if (cs)
                        return none_expr(); // constraint was generated
                    arg_types.push_back(t);
                }
                cache_key k(d.get_name(), arg_types.size(), arg_types.data());
                auto it = m_cache.find(k);
                if (it != m_cache.end()) {
                    if (closed(it->second))
                        return some_expr(::lean::mk_app(it->second, nargs, args));
                    else
                        return some_expr(instantiate(it->second, nargs, args));
                } else {
                    return mk_app_core(d, nargs, args, use_cache);
                }
            }
        }
        return mk_app_core(d, nargs, args, use_cache);
    }

    void push() {
        m_cache.push();
    }

    void pop() {
        m_cache.pop();
    }
};

app_builder::app_builder(type_checker & tc):m_ptr(new imp(tc)) {}
app_builder::~app_builder() {}
optional<expr> app_builder::mk_app(declaration const & d, unsigned nargs, expr const * args, bool use_cache) {
    return m_ptr->mk_app(d, nargs, args, use_cache);
}
optional<expr> app_builder::mk_app(name const & n, unsigned nargs, expr const * args, bool use_cache) {
    declaration const & d = m_ptr->m_tc.env().get(n);
    return mk_app(d, nargs, args, use_cache);
}
optional<expr> app_builder::mk_app(name const & n, std::initializer_list<expr> const & args, bool use_cache) {
    return mk_app(n, args.size(), args.begin(), use_cache);
}
optional<expr> app_builder::mk_app(name const & n, expr const & a1, bool use_cache) {
    return mk_app(n, {a1}, use_cache);
}
optional<expr> app_builder::mk_app(name const & n, expr const & a1, expr const & a2, bool use_cache) {
    return mk_app(n, {a1, a2}, use_cache);
}
optional<expr> app_builder::mk_app(name const & n, expr const & a1, expr const & a2, expr const & a3, bool use_cache) {
    return mk_app(n, {a1, a2, a3}, use_cache);
}
void app_builder::push() { m_ptr->push(); }
void app_builder::pop() { m_ptr->pop(); }

struct lua_app_builder {
    type_checker_ref m_tc;
    app_builder      m_builder;
    lua_app_builder(type_checker_ref const & r):m_tc(r), m_builder(*r.get()) {}
};

typedef std::shared_ptr<lua_app_builder> app_builder_ref;

DECL_UDATA(app_builder_ref)

static int mk_app_builder(lua_State * L) {
    return push_app_builder_ref(L, std::make_shared<lua_app_builder>(to_type_checker_ref(L, 1)));
}

static int app_builder_mk_app(lua_State * L) {
    int nargs = lua_gettop(L);
    buffer<expr> args;
    app_builder & b = to_app_builder_ref(L, 1)->m_builder;
    bool use_cache  = true;
    name n          = to_name_ext(L, 2);
    for (int i = 3; i <= nargs; i++) {
        if (i < nargs || is_expr(L, i))
            args.push_back(to_expr(L, i));
        else
            use_cache = lua_toboolean(L, i);
    }
    return push_optional_expr(L, b.mk_app(n, args.size(), args.data(), use_cache));
}

static int app_builder_push(lua_State * L) {
    to_app_builder_ref(L, 1)->m_builder.push();
    return 0;
}

static int app_builder_pop(lua_State * L) {
    to_app_builder_ref(L, 1)->m_builder.pop();
    return 0;
}

static const struct luaL_Reg app_builder_ref_m[] = {
    {"__gc",    app_builder_ref_gc},
    {"mk_app",  safe_function<app_builder_mk_app>},
    {"push",    safe_function<app_builder_push>},
    {"pop",     safe_function<app_builder_pop>},
    {0, 0}
};

void open_app_builder(lua_State * L) {
    luaL_newmetatable(L, app_builder_ref_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, app_builder_ref_m, 0);

    SET_GLOBAL_FUN(mk_app_builder,       "app_builder");
    SET_GLOBAL_FUN(app_builder_ref_pred, "is_app_builder");
}
}
