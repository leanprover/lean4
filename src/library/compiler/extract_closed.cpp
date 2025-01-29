/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "runtime/flet.h"
#include "kernel/instantiate.h"
#include "kernel/expr_maps.h"
#include "kernel/for_each_fn.h"
#include "kernel/inductive.h"
#include "kernel/trace.h"
#include "library/compiler/util.h"
#include "library/compiler/closed_term_cache.h"
#include "library/compiler/reduce_arity.h"

namespace lean {
name mk_extract_closed_aux_fn(name const & n, unsigned idx) {
    return name(n, "_closed").append_after(idx);
}

bool is_extract_closed_aux_fn(name const & n) {
    if (!n.is_string() || n.is_atomic()) return false;
    return strncmp(n.get_string().data(), "_closed", 7) == 0;
}

class extract_closed_fn {
    elab_environment    m_env;
    comp_decls          m_input_decls;
    name_generator      m_ngen;
    local_ctx           m_lctx;
    buffer<comp_decl>   m_new_decls;
    name                m_base_name;
    unsigned            m_next_idx{1};
    expr_map<bool>      m_closed;

    elab_environment const & env() const { return m_env; }
    name_generator & ngen() { return m_ngen; }

    name next_name() {
        name r = mk_extract_closed_aux_fn(m_base_name, m_next_idx);
        m_next_idx++;
        return r;
    }

    expr find(expr const & e) {
        if (is_fvar(e)) {
            if (optional<local_decl> decl = m_lctx.find_local_decl(e)) {
                if (optional<expr> v = decl->get_value()) {
                    return find(*v);
                }
            }
        } else if (is_mdata(e)) {
            return find(mdata_expr(e));
        }
        return e;
    }

    bool in_current_mutual_block(name const & decl_name) {
        for (auto d : m_input_decls)
            if (d.fst() == decl_name)
                return true;
        return false;
    }

    bool is_closed(expr e) {
        switch (e.kind()) {
        case expr_kind::MVar:   lean_unreachable();
        case expr_kind::Pi:     lean_unreachable();
        case expr_kind::Sort:   lean_unreachable();
        case expr_kind::Lit:    return true;
        case expr_kind::BVar:   return true;
        case expr_kind::Const:  return !in_current_mutual_block(const_name(e));
        case expr_kind::MData:  return is_closed(mdata_expr(e));
        case expr_kind::Proj:   return is_closed(proj_expr(e));
        default:
            break;
        };

        auto it = m_closed.find(e);
        if (it != m_closed.end())
            return it->second;

        bool r;
        switch (e.kind()) {
        case expr_kind::FVar:
            if (auto v = m_lctx.get_local_decl(e).get_value()) {
                r = is_closed(*v);
            } else {
                r = false;
            }
            break;
        case expr_kind::App: {
            buffer<expr> args;
            expr const & fn = get_app_args(e, args);
            r = true;
            if (!is_closed(fn)) {
                r = false;
            } else {
                if (is_constant(fn) && has_never_extract_attribute(m_env, const_name(fn))) {
                    r = false;
                } else {
                    for (expr const & arg : args) {
                        if (!is_closed(arg)) {
                            r = false;
                            break;
                        }
                    }
                }
            }
            break;
        }
        case expr_kind::Lambda:
            while (is_lambda(e)) {
                e = binding_body(e);
            }
            r = is_closed(e);
            break;
        case expr_kind::Let:
            r = true;
            while (is_let(e)) {
                if (!is_closed(let_value(e))) {
                    r = false;
                    break;
                }
                e = let_body(e);
            }
            if (r && !is_closed(e)) {
                r = false;
            }
            break;
        default:
            lean_unreachable();
        }
        m_closed.insert(mk_pair(e, r));
        return r;
    }

    expr visit_lambda(expr e) {
        flet<local_ctx> save_lctx(m_lctx, m_lctx);
        buffer<expr> fvars;
        while (is_lambda(e)) {
            lean_assert(!has_loose_bvars(binding_domain(e)));
            expr new_fvar = m_lctx.mk_local_decl(ngen(), binding_name(e), binding_domain(e));
            fvars.push_back(new_fvar);
            e = binding_body(e);
        }
        expr r = visit(instantiate_rev(e, fvars.size(), fvars.data()));
        return m_lctx.mk_lambda(fvars, r);
    }


    bool is_neutral_constructor_app(expr const & e) {
        if (!is_constructor_app(env(), e)) return false;
        buffer<expr> args;
        get_app_args(e, args);
        for (expr const & arg : args) {
            if (!is_enf_neutral(arg))
                return false;
        }
        return true;
    }

    void collect_deps(expr e, name_set & collected, buffer<expr> & fvars) {
        buffer<expr> todo;
        while (true) {
            for_each(e, [&](expr const & x, unsigned) {
                    if (!has_fvar(x)) return false;
                    if (is_fvar(x) && !collected.contains(fvar_name(x))) {
                        collected.insert(fvar_name(x));
                        optional<expr> v = m_lctx.get_local_decl(x).get_value();
                        lean_assert(v);
                        fvars.push_back(x);
                        todo.push_back(*v);
                    }
                    return true;
                });
            if (todo.empty())
                return;
            e = todo.back();
            todo.pop_back();
        }
    }

    void collect_deps(expr e, buffer<expr> & fvars) {
        name_set collected;
        collect_deps(e, collected, fvars);
        sort_fvars(m_lctx, fvars);
    }

    bool arity_eq_0(name c) {
        c = mk_cstage2_name(c);
        optional<constant_info> info = env().find(c);
        if (!info || !info->is_definition()) return false;
        return !is_lambda(info->get_value());
    }

    bool is_join_point_app(expr const & e) const {
        if (!is_app(e)) return false;
        expr const & fn = get_app_fn(e);
        return
            is_fvar(fn) &&
            is_join_point_name(m_lctx.get_local_decl(fn).get_user_name());
    }

    expr mk_aux_constant(expr const & e0) {
        expr e = find(e0);
        if (is_enf_neutral(e) || is_enf_unreachable(e)) {
            return e0;
        }
        if (is_join_point_app(e)) {
            return e0;
        }
        if (is_constant(e) && arity_eq_0(const_name(e))) {
            /* Remarr: if a constant `C` has arity > 0, then it is worth creating a new constant with arity 0 that
               just returns `C`. In this way, we cache the closure allocation.
               To implement this optimization we need to first store the definitions after erasure. */
            return e0;
        }
        if (is_neutral_constructor_app(e)) {
            /* We don't create auxiliary constants for constructor applications such as:
               `none ◾` and `list.nil ◾` */
            return e0;
        }
        if (is_lit(e) && lit_value(e).kind() == literal_kind::Nat && lit_value(e).get_nat().is_small()) {
            /* We don't create auxiliary constants for small nat literals. Reason: they are cheap. */
            return e0;
        }
        if (!is_lit(e) && is_morally_num_lit(e)) {
            /* We don't create auxiliary constants for uint* literals. */
            return e0;
        }
        buffer<expr> fvars;
        collect_deps(e, fvars);
        e = m_lctx.mk_lambda(fvars, e);
        lean_assert(!has_loose_bvars(e));
        if (optional<name> c = get_closed_term_name(m_env, e)) {
            return mk_constant(*c);
        }
        name c = next_name();
        m_new_decls.push_back(comp_decl(c, e));
        m_env = cache_closed_term_name(m_env, e, c);
        return mk_constant(c);
    }

    expr visit_let(expr e) {
        flet<local_ctx> save_lctx(m_lctx, m_lctx);
        buffer<expr> fvars;
        while (is_let(e)) {
            lean_assert(!has_loose_bvars(let_type(e)));
            expr new_val  = visit(instantiate_rev(let_value(e), fvars.size(), fvars.data()));
            expr new_fvar = m_lctx.mk_local_decl(ngen(), let_name(e), let_type(e), new_val);
            fvars.push_back(new_fvar);
            e = let_body(e);
        }
        expr r = visit(instantiate_rev(e, fvars.size(), fvars.data()));
        return m_lctx.mk_lambda(fvars, r);
    }

    expr visit_app(expr const & e) {
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);
        for (unsigned i = 0; i < args.size(); i++) {
            args[i] = visit(args[i]);
        }
        expr r = mk_app(fn, args);
        if (is_closed(r))
            return mk_aux_constant(r);
        else
            return r;
    }

    expr visit_atom(expr const & e) {
        return mk_aux_constant(e);
    }

    expr visit(expr const & e) {
        switch (e.kind()) {
        case expr_kind::Lit:    return visit_atom(e);
        case expr_kind::Const:  return visit_atom(e);
        case expr_kind::App:    return visit_app(e);
        case expr_kind::Lambda: return visit_lambda(e);
        case expr_kind::Let:    return visit_let(e);
        default:                return e;
        }
    }

public:
    extract_closed_fn(elab_environment const & env, comp_decls const & ds):
        m_env(env), m_input_decls(ds) {
    }

    pair<elab_environment, comp_decls> operator()(comp_decl const & d) {
        if (arity_was_reduced(d)) {
            /* Do nothing since `d` will be inlined. */
            return mk_pair(env(), comp_decls(d));
        }
        expr v      = d.snd();
        if (is_extract_closed_aux_fn(d.fst())) {
            /* Do not extract closed terms from an auxiliary declaration created by this module. */
            return mk_pair(env(), comp_decls(d));
        }
        m_base_name = d.fst();
        expr new_v  = visit(v);
        comp_decl new_d(d.fst(), new_v);
        m_new_decls.push_back(new_d);
        return mk_pair(env(), comp_decls(m_new_decls));
    }
};

pair<elab_environment, comp_decls> extract_closed_core(elab_environment const & env, comp_decls const & input_ds, comp_decl const & d) {
    return extract_closed_fn(env, input_ds)(d);
}

pair<elab_environment, comp_decls> extract_closed(elab_environment env, comp_decls const & ds) {
    comp_decls r;
    for (comp_decl const & d : ds) {
        comp_decls new_ds;
        std::tie(env, new_ds) = extract_closed_core(env, ds, d);
        r = append(r, new_ds);
    }
    return mk_pair(env, r);
}
}
