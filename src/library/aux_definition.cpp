/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "kernel/type_checker.h"
#include "kernel/replace_fn.h"
#include "library/locals.h"
#include "library/module.h"
#include "library/trace.h"
#include "library/aux_definition.h"
#include "library/unfold_macros.h"
namespace lean {
struct mk_aux_definition_fn {
    type_context &  m_ctx;
    name            m_prefix;
    unsigned        m_next_idx;
    name_set        m_found_univ_params;
    name_map<level> m_univ_meta_to_param;
    name_map<level> m_univ_meta_to_param_inv;
    name_set        m_found_local;
    name_map<expr>  m_meta_to_param;
    name_map<expr>  m_meta_to_param_inv;
    buffer<name>    m_level_params;
    buffer<expr>    m_params;

    mk_aux_definition_fn(type_context & ctx):
        m_ctx(ctx),
        m_prefix("_aux_param"),
        m_next_idx(0) {}

    level collect(level const & l) {
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
                    name const & id = param_id(l);
                    if (!m_found_univ_params.contains(id)) {
                        m_found_univ_params.insert(id);
                        m_level_params.push_back(id);
                    }
                }
                return none_level();
            });
    }

    levels collect(levels const & ls) {
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

    expr collect(expr const & e) {
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

    /* Collect (and sort) dependencies of collected parameters */
    void collect_and_normalize_dependencies(buffer<expr> & norm_params) {
        name_map<expr> new_types;
        for (unsigned i = 0; i < m_params.size(); i++) {
            expr x = m_params[i];
            expr new_type = collect(m_ctx.instantiate_mvars(m_ctx.infer(x)));
            new_types.insert(mlocal_name(x), new_type);
        }
        local_context const & lctx = m_ctx.lctx();
        std::sort(m_params.begin(), m_params.end(), [&](expr const & l1, expr const & l2) {
                return lctx.get_local_decl(l1)->get_idx() < lctx.get_local_decl(l2)->get_idx();
            });
        for (unsigned i = 0; i < m_params.size(); i++) {
            expr x         = m_params[i];
            expr type      = *new_types.find(mlocal_name(x));
            expr new_type  = replace_locals(type, i, m_params.data(), norm_params.data());
            expr new_param = m_ctx.push_local(local_pp_name(x), new_type, local_info(x));
            norm_params.push_back(new_param);
        }
    }

    pair<environment, expr> operator()(name const & c, expr const & type, expr const & value, bool is_lemma, optional<bool> const & is_meta) {
        lean_assert(!is_lemma || is_meta);
        lean_assert(!is_lemma || *is_meta == false);
        expr new_type  = collect(m_ctx.instantiate_mvars(type));
        expr new_value = collect(m_ctx.instantiate_mvars(value));
        environment const & env = m_ctx.env();
        buffer<expr> norm_params;
        collect_and_normalize_dependencies(norm_params);
        new_type  = replace_locals(new_type, m_params, norm_params);
        new_value = replace_locals(new_value, m_params, norm_params);
        expr def_type  = m_ctx.mk_pi(norm_params, new_type);
        expr def_value = m_ctx.mk_lambda(norm_params, new_value);
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
            d = mk_theorem(c, to_list(m_level_params), def_type, def_value);
        } else {
            bool use_self_opt = true;
            d = mk_definition(env, c, to_list(m_level_params), def_type, def_value, use_self_opt, !untrusted);
        }
        environment new_env = module::add(env, check(env, d, true));
        buffer<level> ls;
        for (name const & n : m_level_params) {
            if (level const * l = m_univ_meta_to_param_inv.find(n))
                ls.push_back(*l);
            else
                ls.push_back(mk_param_univ(n));
        }
        buffer<expr> ps;
        for (expr const & x : m_params) {
            if (expr const * m = m_meta_to_param_inv.find(mlocal_name(x)))
                ps.push_back(*m);
            else
                ps.push_back(x);
        }
        expr r = mk_app(mk_constant(c, to_list(ls)), ps);
        return mk_pair(new_env, r);
    }
};

pair<environment, expr> mk_aux_definition(environment const & env, metavar_context const & mctx, local_context const & lctx,
                                          name const & c, expr const & type, expr const & value, optional<bool> const & is_meta) {
    type_context ctx(env, options(), mctx, lctx, transparency_mode::All);
    bool is_lemma = false;
    return mk_aux_definition_fn(ctx)(c, type, value, is_lemma, is_meta);
}

pair<environment, expr> mk_aux_definition(environment const & env, metavar_context const & mctx, local_context const & lctx,
                                          name const & c, expr const & value, optional<bool> const & is_meta) {
    type_context ctx(env, options(), mctx, lctx, transparency_mode::All);
    expr type     = ctx.infer(value);
    bool is_lemma = false;
    return mk_aux_definition_fn(ctx)(c, type, value, is_lemma, is_meta);
}

pair<environment, expr> mk_aux_lemma(environment const & env, metavar_context const & mctx, local_context const & lctx,
                                     name const & c, expr const & type, expr const & value) {
    type_context ctx(env, options(), mctx, lctx, transparency_mode::All);
    bool is_lemma = true;
    optional<bool> is_meta(false);
    return mk_aux_definition_fn(ctx)(c, type, value, is_lemma, is_meta);
}
}
