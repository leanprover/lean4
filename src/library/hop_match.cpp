/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/optional.h"
#include "util/buffer.h"
#include "kernel/free_vars.h"
#include "kernel/instantiate.h"
#include "kernel/kernel.h"
#include "kernel/for_each_fn.h"
#include "kernel/replace_visitor.h"
#include "library/equality.h"
#include "library/kernel_bindings.h"
#include "library/hop_match.h"

namespace lean {

class hop_match_fn {
    buffer<optional<expr>> & m_subst;
    buffer<expr>             m_vars;
    optional<ro_environment> m_env;
    optional<ro_metavar_env> m_menv;
    name_map<name> *         m_name_subst;

    bool is_free_var(expr const & x, unsigned ctx_size) const {
        return is_var(x) && var_idx(x) >= ctx_size;
    }

    bool is_locally_bound(expr const & x, unsigned ctx_size) const {
        return is_var(x) && var_idx(x) < ctx_size;
    }

    expr lift_free_vars(expr const & e, unsigned d) const { return ::lean::lift_free_vars(e, d, m_menv); }
    expr lower_free_vars(expr const & e, unsigned s, unsigned d) const { return ::lean::lower_free_vars(e, s, d, m_menv); }
    bool has_free_var(expr const & e, unsigned i) const { return ::lean::has_free_var(e, i, m_menv); }
    bool has_free_var(expr const & e, unsigned low, unsigned high) const { return ::lean::has_free_var(e, low, high, m_menv); }
    expr apply_beta(expr f, unsigned num_args, expr const * args) const { return ::lean::apply_beta(f, num_args, args, m_menv); }
    bool has_free_var_ge(expr const & e, unsigned low) const { return ::lean::has_free_var_ge(e, low, m_menv); }

    optional<expr> get_subst(expr const & x, unsigned ctx_size) const {
        lean_assert(is_free_var(x, ctx_size));
        unsigned vidx = var_idx(x) - ctx_size;
        unsigned sz = m_subst.size();
        if (vidx >= sz)
            throw exception("ill-formed higher-order matching problem");
        return m_subst[sz - vidx - 1];
    }

    bool has_locally_bound_var(expr const & t, unsigned ctx_size) const {
        return has_free_var(t, 0, ctx_size);
    }

    void assign(expr const & p, expr const & t, unsigned ctx_size) {
        lean_assert(is_free_var(p, ctx_size));
        lean_assert(!get_subst(p, ctx_size));
        unsigned vidx = var_idx(p) - ctx_size;
        unsigned sz = m_subst.size();
        m_subst[sz - vidx - 1] = t;
    }

    bool args_are_distinct_locally_bound_vars(expr const & p, unsigned ctx_size, buffer<expr> & vars) {
        lean_assert(is_app(p));
        vars.clear();
        unsigned num = num_args(p);
        for (unsigned i = 1; i < num; i++) {
            expr const & v = arg(p, i);
            if (!is_locally_bound(v, ctx_size))
                return false;
            if (std::find(vars.begin(), vars.end(), v) != vars.end())
                return false;
            vars.push_back(v);
        }
        return true;
    }

    /**
       \brief Return t' when all locally bound variables in \c t occur in vars at positions [0, vars_size).
       The locally bound variables occurring in \c t are replaced using the following mapping:

             vars[vars_size - 1] ==> #0
             ...
             vars[0]             ==> #vars_size - 1

       None is returned if \c t contains a locally bound variable that does not occur in \c vars.
       Remark: vars_size <= vars.size()
     */
    optional<expr> proj_core(expr const & t, unsigned ctx_size, buffer<expr> const & vars, unsigned vars_size) {
        bool failed = false;
        expr r = replace(t, [&](expr const & e, unsigned offset) -> expr {
                if (is_var(e)) {
                    unsigned vidx = var_idx(e);
                    if (vidx < offset)
                        return e;
                    vidx -= offset;
                    if (vidx < ctx_size) {
                        // e is locally bound
                        for (unsigned i = 0; i < vars_size; i++) {
                            if (var_idx(vars[i]) == vidx)
                                return mk_var(offset + vars_size - i - 1);
                        }
                        failed = true;
                        return e;
                    } else if (ctx_size != vars_size) {
                        return mk_var(offset + vidx - ctx_size + vars_size);
                    } else {
                        return e;
                    }
                } else {
                    return e;
                }
            });
        if (failed)
            return none_expr();
        else
            return some_expr(r);
    }

    // We say \c t has a simple projection when it is of the form (f v1 ... vn)
    // where f does no contain locally bound variables, and v1 ... vn are exactly the variables in vars.
    // In this case, the proj procedure can return f instead of (fun xn .... x1, f x1 ... xn)
    bool is_simple_proj(expr const & t, unsigned ctx_size, buffer<expr> const & vars) {
        if (is_app(t) && !has_locally_bound_var(arg(t, 0), ctx_size) && num_args(t) == vars.size() + 1) {
            for (unsigned i = 0; i < vars.size(); i++)
                if (arg(t, i+1) != vars[i])
                    return false;
            return true;
        } else {
            return false;
        }
    }

    /**
       \brief Return <tt>(fun (x1 ... xn) t')</tt> if all locally bound variables in \c t occur in vars.
       \c n is the size of \c vars.
       None is returned if \c t contains a locally bound variable that does not occur in \c vars.
    */
    optional<expr> proj(expr const & t, context const & ctx, unsigned ctx_size, buffer<expr> const & vars) {
        if (is_simple_proj(t, ctx_size, vars)) {
            return some_expr(lower_free_vars(arg(t, 0), ctx_size, ctx_size));
        }
        optional<expr> t_prime = proj_core(t, ctx_size, vars, vars.size());
        if (!t_prime)
            return none_expr();
        expr r     = *t_prime;
        unsigned i = vars.size();
        while (i > 0) {
            --i;
            unsigned vidx = var_idx(vars[i]);
            auto p = lookup_ext(ctx, vidx);
            context_entry const & entry = p.first;
            context entry_ctx = p.second;
            if (!entry.get_domain())
                return none_expr();
            expr d     = *entry.get_domain();
            optional<expr> new_d = proj_core(d, entry_ctx.size(), vars, i);
            if (!new_d)
                return none_expr();
            r = mk_lambda(entry.get_name(), *new_d, r);
        }
        return some_expr(r);
    }

    optional<expr> unfold_constant(expr const & c) {
        if (is_constant(c)) {
            auto obj = (*m_env)->find_object(const_name(c));
            if (obj && (obj->is_definition() || obj->is_builtin()))
                return some_expr(obj->get_value());
        }
        return none_expr();
    }

    bool match_constant(expr const & p, expr const & t) {
        if (p == t)
            return true;
        auto new_p = unfold_constant(p);
        if (new_p)
            return match_constant(*new_p, t);
        return false;
    }

    /**
       \brief Return true iff all free variables in the pattern \c p are assigned.
    */
    bool all_free_vars_are_assigned(expr const & p, unsigned ctx_size) const {
        bool result = true;
        for_each(p, [&](expr const & v, unsigned offset) {
                if (!result)
                    return false;
                if (is_var(v) && this->is_free_var(v, ctx_size + offset) && !get_subst(v, ctx_size + offset)) {
                    result = false;
                }
                return true;
            });
        return result;
    }

    /**
       \brief Auxiliary functional object for instantiating the free variables in a pattern.
    */
    class instantiate_free_vars_proc : public replace_visitor {
    protected:
        hop_match_fn &  m_ref;
        unsigned        m_ctx_size;

        virtual expr visit_var(expr const & x, context const & ctx) {
            unsigned real_ctx_sz = ctx.size() + m_ctx_size;
            if (m_ref.is_free_var(x, real_ctx_sz)) {
                optional<expr> r = m_ref.get_subst(x, real_ctx_sz);
                lean_assert(r);
                return m_ref.lift_free_vars(*r, real_ctx_sz);
            } else {
                return x;
            }
        }

        virtual expr visit_app(expr const & e, context const & ctx) {
            unsigned real_ctx_sz = ctx.size() + m_ctx_size;
            expr const & f = arg(e, 0);
            if (is_var(f) && m_ref.is_free_var(f, real_ctx_sz)) {
                buffer<expr> new_args;
                for (unsigned i = 0; i < num_args(e); i++)
                    new_args.push_back(visit(arg(e, i), ctx));
                if (is_lambda(new_args[0]))
                    return m_ref.apply_beta(new_args[0], new_args.size() - 1, new_args.data() + 1);
                else
                    return mk_app(new_args);
            } else {
                return replace_visitor::visit_app(e, ctx);
            }
        }

    public:
        instantiate_free_vars_proc(hop_match_fn & fn, unsigned ctx_size):
            m_ref(fn), m_ctx_size(ctx_size) {
        }
    };

    bool match(expr const & p, expr const & t, context const & ctx, unsigned ctx_size) {
        lean_assert(ctx.size() == ctx_size);
        if (is_free_var(p, ctx_size)) {
            auto s = get_subst(p, ctx_size);
            if (s) {
                return lift_free_vars(*s, ctx_size) == t;
            } else if (has_locally_bound_var(t, ctx_size)) {
                return false;
            } else {
                assign(p, lower_free_vars(t, ctx_size, ctx_size), ctx_size);
                return true;
            }
        } else if (is_app(p) && is_free_var(arg(p, 0), ctx_size)) {
            if (args_are_distinct_locally_bound_vars(p, ctx_size, m_vars)) {
                // higher-order pattern case
                auto s = get_subst(arg(p, 0), ctx_size);
                unsigned num = num_args(p);
                if (s) {
                    expr f     = lift_free_vars(*s, ctx_size);
                    expr new_p = apply_beta(f, num - 1, &(arg(p, 1)));
                    return new_p == t;
                } else {
                    optional<expr> new_t = proj(t, ctx, ctx_size, m_vars);
                    if (new_t) {
                        assign(arg(p, 0), *new_t, ctx_size);
                        return true;
                    }
                }
            } else if (all_free_vars_are_assigned(p, ctx_size)) {
                instantiate_free_vars_proc proc(*this, ctx_size);
                expr new_p = proc(p);
                return new_p == t;
            }
            // fallback to the first-order case
        }

        if (p == t && !has_free_var_ge(p, ctx_size)) {
            return true;
        }

        if (m_env && is_constant(p)) {
            return match_constant(p, t);
        }

        if (p.kind() != t.kind())
            return false;
        switch (p.kind()) {
        case expr_kind::Var: case expr_kind::Constant: case expr_kind::Type:
        case expr_kind::Value: case expr_kind::MetaVar:
            return false;
        case expr_kind::App: {
            unsigned i1 = num_args(p);
            unsigned i2 = num_args(t);
            while (i1 > 0 && i2 > 0) {
                --i1;
                --i2;
                if (i1 == 0 && i2 > 0) {
                    return match(arg(p, i1), mk_app(i2+1, begin_args(t)), ctx, ctx_size);
                } else if (i2 == 0 && i1 > 0) {
                    return match(mk_app(i1+1, begin_args(p)), arg(t, i2), ctx, ctx_size);
                } else {
                    if (!match(arg(p, i1), arg(t, i2), ctx, ctx_size))
                        return false;
                }
            }
            return true;
        }
        case expr_kind::Lambda: case expr_kind::Pi:
            if (m_name_subst)
                (*m_name_subst)[abst_name(p)] = abst_name(t);
            return
                match(abst_domain(p), abst_domain(t), ctx, ctx_size) &&
                match(abst_body(p), abst_body(t), extend(ctx, abst_name(t), abst_domain(t)), ctx_size+1);
        case expr_kind::Let:
            // TODO(Leo)
            return false;
        }
        lean_unreachable();
    }
public:
    hop_match_fn(buffer<optional<expr>> & subst, optional<ro_environment> const & env,
                 optional<ro_metavar_env> const & menv, name_map<name> * name_subst):
        m_subst(subst), m_env(env), m_menv(menv), m_name_subst(name_subst) {}

    bool operator()(expr const & p, expr const & t) {
        return match(p, t, context(), 0);
    }
};

bool hop_match(expr const & p, expr const & t, buffer<optional<expr>> & subst, optional<ro_environment> const & env,
               optional<ro_metavar_env> const & menv, name_map<name> * name_subst) {
    return hop_match_fn(subst, env, menv, name_subst)(p, t);
}

static int hop_match_core(lua_State * L, optional<ro_environment> const & env) {
    int nargs = lua_gettop(L);
    expr p    = to_expr(L, 1);
    expr t    = to_expr(L, 2);
    int k     = 0;
    optional<ro_metavar_env> menv;
    if (nargs >= 4 && !lua_isnil(L, 4))
        menv = to_metavar_env(L, 4);
    if (nargs >= 5) {
        k = luaL_checkinteger(L, 5);
        if (k < 0)
            throw exception("hop_match, arg #4 must be non-negative");
    } else {
        k = free_var_range(p);
    }
    buffer<optional<expr>> subst;
    subst.resize(k);
    if (hop_match(p, t, subst, env, menv)) {
        lua_newtable(L);
        int i = 1;
        for (auto s : subst) {
            if (s) {
                push_expr(L, *s);
            } else {
                lua_pushboolean(L, false);
            }
            lua_rawseti(L, -2, i);
            i = i + 1;
        }
    } else {
        lua_pushnil(L);
    }
    return 1;
}

static int hop_match(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs >= 3) {
        if (!lua_isnil(L, 3)) {
            ro_shared_environment env(L, 3);
            return hop_match_core(L, optional<ro_environment>(env));
        } else {
            return hop_match_core(L, optional<ro_environment>());
        }
    } else {
        ro_shared_environment env(L);
        return hop_match_core(L, optional<ro_environment>(env));
    }
}

void open_hop_match(lua_State * L) {
    SET_GLOBAL_FUN(hop_match, "hop_match");
}
}
