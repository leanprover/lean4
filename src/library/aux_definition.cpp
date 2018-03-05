/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "kernel/type_checker.h"
#include "kernel/replace_fn.h"
#include "library/locals.h"
#include "library/placeholder.h"
#include "library/module.h"
#include "library/trace.h"
#include "library/aux_definition.h"
#include "library/unfold_macros.h"
#include "library/replace_visitor_with_tc.h"

namespace lean {
level closure_helper::collect(level const & l) {
    lean_assert(!m_finalized_collection);
    return replace(l, [&](level const & l) {
            if (is_meta(l)) {
                name const & id = meta_id(l);
                if (auto r = m_univ_meta_to_param.find(id)) {
                    return some_level(*r);
                } else {
                    name n      = m_prefix.append_after(m_next_idx);
                    m_next_idx++;
                    level new_r = mk_param_univ(n);
                    m_univ_meta_to_param.insert(id, new_r);
                    m_univ_meta_to_param_inv.insert(n, l);
                    m_level_params.push_back(n);
                    return some_level(new_r);
                }
            } else if (is_param(l)) {
                lean_assert(!is_placeholder(l));
                name const & id = param_id(l);
                if (!m_found_univ_params.contains(id)) {
                    m_found_univ_params.insert(id);
                    m_level_params.push_back(id);
                }
            }
            return none_level();
        });
}

levels closure_helper::collect(levels const & ls) {
    lean_assert(!m_finalized_collection);
    bool modified = false;
    buffer<level> r;
    for (level const & l : ls) {
        level new_l = collect(l);
        if (new_l != l) modified = true;
        r.push_back(new_l);
    }
    if (!modified)
        return ls;
    else
        return to_list(r);
}

expr closure_helper::collect(expr const & e) {
    lean_assert(!m_finalized_collection);
    return replace(e, [&](expr const & e, unsigned) {
            if (is_metavar(e)) {
                name const & id = mlocal_name(e);
                if (auto r = m_meta_to_param.find(id)) {
                    return some_expr(*r);
                } else {
                    expr type  = m_ctx.infer(e);
                    expr x     = m_ctx.push_local("_x", type);
                    m_meta_to_param.insert(id, x);
                    m_meta_to_param_inv.insert(mlocal_name(x), e);
                    m_params.push_back(x);
                    return some_expr(x);
                }
            } else if (is_local(e)) {
                name const & id = mlocal_name(e);
                if (!m_found_local.contains(id)) {
                    m_found_local.insert(id);
                    m_params.push_back(e);
                }
            } else if (is_sort(e)) {
                return some_expr(update_sort(e, collect(sort_level(e))));
            } else if (is_constant(e)) {
                return some_expr(update_constant(e, collect(const_levels(e))));
            }
            return none_expr();
        });
}

void closure_helper::finalize_collection() {
    lean_assert(!m_finalized_collection);
    std::sort(m_level_params.begin(), m_level_params.end());
    name_map<expr> new_types;
    for (unsigned i = 0; i < m_params.size(); i++) {
        expr x = m_params[i];
        expr new_type = collect(zeta_expand(m_ctx.lctx(), m_ctx.instantiate_mvars(m_ctx.infer(x))));
        new_types.insert(mlocal_name(x), new_type);
    }
    local_context const & lctx = m_ctx.lctx();
    std::sort(m_params.begin(), m_params.end(), [&](expr const & l1, expr const & l2) {
            return lctx.get_local_decl(l1).get_idx() < lctx.get_local_decl(l2).get_idx();
        });
    for (unsigned i = 0; i < m_params.size(); i++) {
        expr x         = m_params[i];
        expr type      = *new_types.find(mlocal_name(x));
        expr new_type  = replace_locals(type, i, m_params.data(), m_norm_params.data());
        expr new_param = m_ctx.push_local(mlocal_pp_name(x), new_type, local_info(x));
        m_norm_params.push_back(new_param);
    }
    m_finalized_collection = true;
}

expr closure_helper::mk_pi_closure(expr const & e) {
    lean_assert(m_finalized_collection);
    expr new_e  = replace_locals(e, m_params, m_norm_params);
    return m_ctx.mk_pi(m_norm_params, new_e);
}

expr closure_helper::mk_lambda_closure(expr const & e) {
    lean_assert(m_finalized_collection);
    expr new_e  = replace_locals(e, m_params, m_norm_params);
    return m_ctx.mk_lambda(m_norm_params, new_e);
}

void closure_helper::get_level_closure(buffer<level> & ls) {
    lean_assert(m_finalized_collection);
    for (name const & n : m_level_params) {
        if (level const * l = m_univ_meta_to_param_inv.find(n))
            ls.push_back(*l);
        else
            ls.push_back(mk_param_univ(n));
    }
}

void closure_helper::get_expr_closure(buffer<expr> & ps) {
    lean_assert(m_finalized_collection);
    for (expr const & x : m_params) {
        if (expr const * m = m_meta_to_param_inv.find(mlocal_name(x)))
            ps.push_back(*m);
        else
            ps.push_back(x);
    }
}

buffer<expr> const & closure_helper::get_norm_closure_params() const {
    lean_assert(m_finalized_collection);
    return m_norm_params;
}

struct mk_aux_definition_fn : public closure_helper {
    mk_aux_definition_fn(type_context_old & ctx):closure_helper(ctx) {}

    pair<environment, expr> operator()(name const & c, expr const & type, expr const & value, bool is_lemma, optional<bool> const & is_meta) {
        lean_assert(!is_lemma || is_meta);
        lean_assert(!is_lemma || *is_meta == false);
        expr new_type  = collect(ctx().instantiate_mvars(type));
        expr new_value = collect(ctx().instantiate_mvars(value));
        environment env = ctx().env();
        finalize_collection();
        expr def_type  = mk_pi_closure(new_type);
        expr def_value = mk_lambda_closure(new_value);
        bool untrusted = false;
        if (is_meta)
            untrusted = *is_meta;
        else
            untrusted = use_untrusted(env, def_type) || use_untrusted(env, def_value);
        if (!untrusted) {
            def_type  = unfold_untrusted_macros(env, def_type);
            def_value = unfold_untrusted_macros(env, def_value);
        }
        declaration d;
        if (is_lemma) {
            d = mk_theorem(c, get_norm_level_names(), def_type, def_value);
        } else {
            bool use_self_opt = true;
            d = mk_definition(env, c, get_norm_level_names(), def_type, def_value, use_self_opt, !untrusted);
        }
        environment new_env = module::add(env, check(env, d, true));
        buffer<level> ls;
        get_level_closure(ls);
        buffer<expr> ps;
        get_expr_closure(ps);
        expr r = mk_app(mk_constant(c, to_list(ls)), ps);
        return mk_pair(new_env, r);
    }
};

pair<environment, expr> mk_aux_definition(environment const & env, metavar_context const & mctx, local_context const & lctx,
                                          name const & c, expr const & type, expr const & value, optional<bool> const & is_meta) {
    type_context_old ctx(env, options(), mctx, lctx, transparency_mode::All);
    bool is_lemma = false;
    return mk_aux_definition_fn(ctx)(c, type, value, is_lemma, is_meta);
}

pair<environment, expr> mk_aux_definition(environment const & env, metavar_context const & mctx, local_context const & lctx,
                                          name const & c, expr const & value, optional<bool> const & is_meta) {
    type_context_old ctx(env, options(), mctx, lctx, transparency_mode::All);
    expr type     = ctx.infer(value);
    bool is_lemma = false;
    return mk_aux_definition_fn(ctx)(c, type, value, is_lemma, is_meta);
}

pair<environment, expr> mk_aux_lemma(environment const & env, metavar_context const & mctx, local_context const & lctx,
                                     name const & c, expr const & type, expr const & value) {
    type_context_old ctx(env, options(), mctx, lctx, transparency_mode::All);
    bool is_lemma = true;
    optional<bool> is_meta(false);
    return mk_aux_definition_fn(ctx)(c, type, value, is_lemma, is_meta);
}

struct abstract_nested_proofs_fn : public replace_visitor_with_tc {
    name     m_base_name;
    unsigned m_idx{1};

    abstract_nested_proofs_fn(type_context_old & ctx, name const & b):
        replace_visitor_with_tc(ctx),
        m_base_name(b, "_proof") {
    }

    static bool is_atomic(expr const & e) {
        return is_constant(e) || is_local(e);
    }

    name mk_name() {
        environment env = m_ctx.env();
        while (true) {
            name curr = m_base_name.append_after(m_idx);
            m_idx++;
            if (!env.find(curr)) {
                m_ctx.set_env(env);
                return curr;
            }
        }
    }

    optional<expr> is_non_trivial_proof(expr const & e) {
        if (is_atomic(e))
            return none_expr();
        if (is_pi(e) || is_sort(e))
            return none_expr();
        expr type = m_ctx.infer(e);
        if (!m_ctx.is_prop(type))
            return none_expr();
        if (is_app(e)) {
            buffer<expr> args;
            expr const & fn = get_app_args(e, args);
            if (!is_atomic(fn))
                return some_expr(type);
            for (expr const & arg : args) {
                if (!is_atomic(arg))
                    return some_expr(type);
            }
            return none_expr();
        } else {
            return some_expr(type);
        }
    }

    virtual expr visit_mlocal(expr const & e) override {
        return e;
    }

    virtual expr visit(expr const & e) override {
        if (auto type = is_non_trivial_proof(e)) {
            expr new_e = zeta_expand(m_ctx.lctx(), e);
            if (e != new_e) {
                *type = m_ctx.infer(new_e);
            }
            name n = mk_name();
            auto new_env_new_e = mk_aux_lemma(m_ctx.env(), m_ctx.mctx(), m_ctx.lctx(), n, *type, new_e);
            m_ctx.set_env(new_env_new_e.first);
            return new_env_new_e.second;
        } else {
            return replace_visitor_with_tc::visit(e);
        }
    }

    pair<environment, expr> operator()(expr const & e) {
        expr new_e = replace_visitor_with_tc::operator()(e);
        return mk_pair(m_ctx.env(), new_e);
    }
};

pair<environment, expr> abstract_nested_proofs(environment const & env, metavar_context const & mctx, local_context const & lctx, name const & base_name, expr const & e) {
    type_context_old ctx(env, options(), mctx, lctx, transparency_mode::Semireducible);
    return abstract_nested_proofs_fn(ctx, base_name)(e);
}

pair<environment, expr> abstract_nested_proofs(environment const & env, name const & base_name, expr const & e) {
    lean_assert(!has_metavar(e));
    return abstract_nested_proofs(env, metavar_context(), local_context(), base_name, e);
}
}
