/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/flet.h"
#include "util/interrupt.h"
#include "kernel/instantiate.h"
#include "library/idx_metavar.h"
#include "library/reducible.h"
#include "library/type_context.h"

namespace lean {
/* TODO(Leo): delete this class as soon as we finish porting kernel to abstract type_context */
struct type_context_as_extension_context : public extension_context {
    type_context & m_owner;

    type_context_as_extension_context(type_context & o):m_owner(o) {}

    virtual environment const & env() const { return m_owner.env(); }

    virtual pair<expr, constraint_seq> whnf(expr const & e) {
        return mk_pair(m_owner.whnf(e), constraint_seq());
    }

    virtual pair<bool, constraint_seq> is_def_eq(expr const & e1, expr const & e2, delayed_justification &) {
        return mk_pair(m_owner.is_def_eq(e1, e2), constraint_seq());
    }

    virtual pair<expr, constraint_seq> check_type(expr const & e, bool) {
        return mk_pair(m_owner.infer(e), constraint_seq());
    }

    virtual optional<expr> is_stuck(expr const & e) {
        return m_owner.is_stuck(e);
    }
};

type_context_cache::type_context_cache(environment const & env, options const & opts):
    m_env(env),
    m_options(opts),
    m_proj_info(get_projection_info_map(env)),
    m_frozen_mode(false),
    m_local_instances_initialized(false) {
    m_ci_max_depth = 12; // TODO(Leo): fix
}

bool type_context_cache::is_transparent(transparency_mode m, declaration const & d) {
    if (m == transparency_mode::None)
        return false;
    name const & n = d.get_name();
    if (m_proj_info.contains(n))
        return false;
    if (m == transparency_mode::All)
        return true;
    if (d.is_theorem())
        return false;
    auto s = get_reducible_status(m_env, d.get_name());
    if (m == transparency_mode::Reducible && s == reducible_status::Reducible)
        return true;
    if (m == transparency_mode::Semireducible && s != reducible_status::Irreducible)
        return true;
    return false;
}

optional<declaration> type_context_cache::is_transparent(transparency_mode m, name const & n) {
    auto & cache = m_transparency_cache[static_cast<unsigned>(m)];
    auto it = cache.find(n);
    if (it != cache.end()) {
        return it->second;
    }
    optional<declaration> r;
    if (auto d = m_env.find(n)) {
        if (d->is_definition() && is_transparent(m, *d)) {
            r = d;
        }
    }
    cache.insert(mk_pair(n, r));
    return r;
}

bool type_context_cache::should_unfold_macro(expr const &) {
    // TODO(Leo): add predicate
    return true;
}

void type_context::init_core(transparency_mode m) {
    m_used_assignment        = false;
    m_transparency_mode      = m;
    m_tmp_mode               = false;
}

type_context::type_context(metavar_context & mctx, local_context const & lctx, type_context_cache & cache,
                           transparency_mode m):
    m_mctx(mctx), m_lctx(lctx), m_cache(&cache), m_cache_owner(false) {
    init_core(m);
}

type_context::type_context(environment const & env, options const & opts, metavar_context & mctx, local_context const & lctx,
                           transparency_mode m):
    m_mctx(mctx), m_lctx(lctx), m_cache(new type_context_cache(env, opts)), m_cache_owner(true) {
    init_core(m);
}

type_context::~type_context() {
    if (m_cache_owner)
        delete m_cache;
}

name type_context::get_local_pp_name(expr const & e) const {
    lean_assert(is_local(e));
    if (is_local_decl_ref(e))
        return m_lctx.get_local_decl(e)->get_name();
    else
        return local_pp_name(e);
}

expr type_context::push_local(name const & pp_name, expr const & type, binder_info const & bi) {
    return m_lctx.mk_local_decl(pp_name, type, bi);
}

void type_context::pop_local() {
    return m_lctx.pop_local_decl();
}

expr type_context::abstract_locals(expr const & e, unsigned num_locals, expr const * locals) {
    // TODO(Leo)
    return e;
}

/* ---------------------
   Normalization
   -------------------- */

optional<declaration> type_context::is_transparent(name const & n) {
    return m_cache->is_transparent(m_transparency_mode, n);
}

optional<expr> type_context::reduce_projection(expr const & e) {
    expr const & f = get_app_fn(e);
    if (!is_constant(f))
        return none_expr();
    projection_info const * info = m_cache->m_proj_info.find(const_name(f));
    if (!info)
        return none_expr();
    buffer<expr> args;
    get_app_args(e, args);
    if (args.size() <= info->m_nparams)
        return none_expr();
    unsigned mkidx  = info->m_nparams;
    expr const & mk = args[mkidx];
    expr new_mk     = whnf(mk);
    expr const & new_mk_fn = get_app_fn(new_mk);
    if (!is_constant(new_mk_fn) || const_name(new_mk_fn) != info->m_constructor)
        return none_expr();
    buffer<expr> mk_args;
    get_app_args(new_mk, mk_args);
    unsigned i = info->m_nparams + info->m_i;
    if (i >= mk_args.size())
        none_expr();
    expr r = mk_args[i];
    r = mk_app(r, args.size() - mkidx - 1, args.data() + mkidx + 1);
    return some_expr(r);
}

optional<expr> type_context::expand_macro(expr const & e) {
    lean_assert(is_macro(e));
    if (m_cache->should_unfold_macro(e)) {
        type_context_as_extension_context ext(*this);
        return macro_def(e).expand(e, ext);
    } else {
        return none_expr();
    }
}

expr type_context::whnf_core(expr const & e) {
    switch (e.kind()) {
    case expr_kind::Var:      case expr_kind::Sort:
    case expr_kind::Pi:       case expr_kind::Lambda:
    case expr_kind::Constant: case expr_kind::Local:
        /* Remark: we do not unfold Constants and
           Local declarations eagerly in this method */
        return e;
    case expr_kind::Meta:
        if (is_metavar_decl_ref(e)) {
            if (m_mctx.is_assigned(e)) {
                m_used_assignment = true;
                return m_mctx.instantiate(e);
            }
        } else if (is_idx_metavar(e)) {
            unsigned idx = to_meta_idx(e);
            if (idx < m_tmp_eassignment.size()) {
                if (auto v = m_tmp_eassignment[idx]) {
                    m_used_assignment = true;
                    return *v;
                }
            }
        }
        return e;
    case expr_kind::Macro:
        if (auto m = expand_macro(e)) {
            check_system("whnf");
            return whnf_core(*m);
        } else {
            return e;
        }
    case expr_kind::Let:
        check_system("whnf");
        return whnf_core(::lean::instantiate(let_body(e), let_value(e)));
    case expr_kind::App: {
        check_system("whnf");
        buffer<expr> args;
        expr f0 = get_app_rev_args(e, args);
        expr f  = whnf_core(f0);
        if (is_lambda(f)) {
            unsigned m = 1;
            unsigned num_args = args.size();
            while (is_lambda(binding_body(f)) && m < num_args) {
                f = binding_body(f);
                m++;
            }
            lean_assert(m <= num_args);
            return whnf_core(mk_rev_app(::lean::instantiate(binding_body(f), m, args.data() + (num_args - m)),
                                        num_args - m, args.data()));
        } else {
            return f == f0 ? e : whnf_core(mk_rev_app(f, args.size(), args.data()));
        }
    }}
    lean_unreachable();
}

expr type_context::whnf(expr const & e) {
    // TODO(Leo)
    return e;
}

expr type_context::relaxed_whnf(expr const & e) {
    flet<transparency_mode> set(m_transparency_mode, transparency_mode::All);
    return whnf(e);
}

optional<expr> type_context::is_stuck(expr const & e) {
    // TODO(Leo)
    return none_expr();
}

/* ---------------
   Type inference
   --------------- */

expr type_context::infer(expr const & e) {
    // TODO(Leo)
    return e;
}

expr type_context::check(expr const & e) {
    // TODO(Leo)
    return e;
}

/* -------------------------------
   Temporary assignment management
   ------------------------------- */

optional<level> type_context::get_tmp_uvar_assignment(unsigned idx) const {
    lean_assert(m_tmp_mode);
    lean_assert(idx < m_tmp_uassignment.size());
    return m_tmp_uassignment[idx];
}

optional<expr> type_context::get_tmp_mvar_assignment(unsigned idx) const {
    lean_assert(m_tmp_mode);
    lean_assert(idx < m_tmp_eassignment.size());
    return m_tmp_eassignment[idx];
}

optional<level> type_context::get_tmp_assignment(level const & l) const {
    lean_assert(is_idx_metauniv(l));
    return get_tmp_uvar_assignment(to_meta_idx(l));
}

optional<expr> type_context::get_tmp_assignment(expr const & e) const {
    lean_assert(is_idx_metavar(e));
    return get_tmp_mvar_assignment(to_meta_idx(e));
}

void type_context::assign_tmp(level const & u, level const & l) {
    lean_assert(m_tmp_mode);
    lean_assert(is_idx_metauniv(u));
    lean_assert(to_meta_idx(u) < m_tmp_uassignment.size());
    m_tmp_uassignment[to_meta_idx(u)] = l;
}

void type_context::assign_tmp(expr const & m, expr const & v) {
    lean_assert(m_tmp_mode);
    lean_assert(is_idx_metavar(m));
    lean_assert(to_meta_idx(m) < m_tmp_eassignment.size());
    m_tmp_eassignment[to_meta_idx(m)] = v;
}

/* -----------------------------------
   Uniform interface to tmp/regular metavariables
   ----------------------------------- */

bool type_context::is_uvar(level const & l) const {
    if (m_tmp_mode)
        return is_idx_metauniv(l);
    else
        return is_univ_metavar_decl_ref(l);
}

bool type_context::is_mvar(expr const & e) const {
    if (m_tmp_mode)
        return is_idx_metavar(e);
    else
        return is_metavar_decl_ref(e);
}

optional<level> type_context::get_assignment(level const & l) const {
    if (m_tmp_mode)
        return get_tmp_assignment(l);
    else
        return m_mctx.get_assignment(l);
}

optional<expr> type_context::get_assignment(expr const & e) const {
    if (m_tmp_mode)
        return get_tmp_assignment(e);
    else
        return m_mctx.get_assignment(e);
}

void type_context::assign(level const & u, level const & l) {
    if (m_tmp_mode)
        assign_tmp(u, l);
    else
        m_mctx.assign(u, l);
}

void type_context::assign(expr const & m, expr const & v) {
    if (m_tmp_mode)
        assign_tmp(m, v);
    else
        m_mctx.assign(m, v);
}

level type_context::instantiate(level const & l) {
    if (m_tmp_mode) {
        return replace(l, [&](level const & l) {
                if (!has_meta(l)) {
                    return some_level(l);
                } else if (is_idx_metauniv(l)) {
                    if (auto v1 = get_tmp_assignment(l)) {
                        m_used_assignment = true;
                        level v2 = instantiate(*v1);
                        if (*v1 != v2) {
                            assign_tmp(l, v2);
                            return some_level(v2);
                        } else {
                            return some_level(*v1);
                        }
                    }
                }
                return none_level();
            });
    } else {
        level r = m_mctx.instantiate(l);
        if (r != l)
            m_used_assignment = true;
        return r;
    }
}

/* -----------------------------------
   Unification / definitional equality
   ----------------------------------- */

bool type_context::is_def_eq(level const & l1, level const & l2) {
    if (is_equivalent(l1, l2)) {
        return true;
    }

    if (is_uvar(l1)) {
        m_used_assignment = true;
        if (auto v = get_assignment(l1)) {
            return is_def_eq(*v, l2);
        } else {
            assign(l1, l2);
            return true;
        }
    }

    if (is_uvar(l2)) {
        m_used_assignment = true;
        if (auto v = get_assignment(l2)) {
            return is_def_eq(l1, *v);
        } else {
            assign(l2, l1);
            return true;
        }
    }

    level new_l1 = normalize(instantiate(l1));
    level new_l2 = normalize(instantiate(l2));

    if (l1 != new_l1 || l2 != new_l2)
        return is_def_eq(new_l1, new_l2);

    if (l1.kind() != l2.kind())
        return false;

    switch (l1.kind()) {
    case level_kind::Max:
        return
            is_def_eq(max_lhs(l1), max_lhs(l2)) &&
            is_def_eq(max_rhs(l1), max_rhs(l2));
    case level_kind::IMax:
        return
            is_def_eq(imax_lhs(l1), imax_lhs(l2)) &&
            is_def_eq(imax_rhs(l1), imax_rhs(l2));
    case level_kind::Succ:
        return is_def_eq(succ_of(l1), succ_of(l2));
    case level_kind::Param:
    case level_kind::Global:
        return false;
    case level_kind::Zero:
    case level_kind::Meta:
        lean_unreachable();
    }
    lean_unreachable();
}

bool type_context::is_def_eq(levels const & ls1, levels const & ls2) {
    if (is_nil(ls1) && is_nil(ls2)) {
        return true;
    } else if (!is_nil(ls1) && !is_nil(ls2)) {
        return
            is_def_eq(head(ls1), head(ls2)) &&
            is_def_eq(tail(ls1), tail(ls2));
    } else {
        return false;
    }
}


/** \brief Return some definition \c d iff \c e is a target for delta-reduction,
    and the given definition is the one to be expanded. */
optional<declaration> type_context::is_delta(expr const & e) {
    expr const & f = get_app_fn(e);
    if (is_constant(f)) {
        return is_transparent(const_name(f));
    } else {
        return none_declaration();
    }
}



/*
struct unification_hint_fn {
    type_context &           m_owner;
    unification_hint const & m_hint;
    buffer<optional<expr>>   m_assignment;

    unification_hint_fn(type_context & o, unification_hint const & hint):
        m_owner(o), m_hint(hint) {
        m_assignment.resize(m_hint.get_num_vars());
    }

    bool syntactic_match(expr const & pattern, expr const & e) {
        unsigned idx;
        switch (pattern.kind()) {
        case expr_kind::Var:
            idx = var_idx(pattern);
            if (!m_assignment[idx]) {
                m_assignment[idx] = some_expr(e);
                return true;
            } else {
                return m_owner.is_def_eq(*m_assignment[idx], e);
            }
        case expr_kind::Constant:
            return
                is_constant(e) &&
                const_name(pattern) == const_name(e) &&
                m_owner.is_def_eq(const_levels(pattern), const_levels(e));
        case expr_kind::Sort:
            return is_sort(e) && m_owner.is_def_eq(sort_level(pattern), sort_level(e));
        case expr_kind::Pi:    case expr_kind::Lambda:
        case expr_kind::Macro: case expr_kind::Let:
            // Remark: we do not traverse inside of binders.
            return pattern == e;
        case expr_kind::App:
            return
                is_app(e) &&
                syntactic_match(app_fn(pattern), app_fn(e)) &&
                syntactic_match(app_arg(pattern), app_arg(e));
        case expr_kind::Local: case expr_kind::Meta:
            lean_unreachable();
        }
        lean_unreachable();
    }

    bool operator()(expr const & lhs, expr const & rhs) {
        if (!syntactic_match(m_hint.get_lhs(), lhs)) {
            lean_trace(name({"type_context", "unification_hint"}), tout() << "LHS does not match\n";);
            return false;
        } else if (!syntactic_match(m_hint.get_rhs(), rhs)) {
            lean_trace(name({"type_context", "unification_hint"}), tout() << "RHS does not match\n";);
            return false;
        } else {
            buffer<expr>
            auto instantiate_assignment_fn = [&](expr const & e, unsigned offset) {
                if (is_var(e)) {
                    unsigned idx = var_idx(e) + offset;
                    if (idx < m_assignment.size()) {
                        lean_assert(m_assignment[idx]);
                        return m_assignment[idx];
                    }
                }
                return none_expr();
            };
            buffer<expr_pair> constraints;
            to_buffer(m_hint.get_constraints(), constraints);
            for (expr_pair const & p : constraints) {
                expr new_lhs = replace(p.first, instantiate_assignment_fn);
                expr new_rhs = replace(p.second, instantiate_assignment_fn);
                expr new_lhs_inst = m_owner.instantiate_uvars_mvars(new_lhs);
                expr new_rhs_inst = m_owner.instantiate_uvars_mvars(new_rhs);
                bool success = m_owner.is_def_eq(new_lhs, new_rhs);
                lean_trace(name({"type_context", "unification_hint"}),
                           tout() << new_lhs_inst << " =?= " << new_rhs_inst << "..."
                           << (success ? "success" : "failed") << "\n";);
                if (!success) return false;
            }
            lean_trace(name({"type_context", "unification_hint"}),
                       tout() << "hint successfully applied\n";);
            return true;
        }
    }
};

bool old_type_context::try_unification_hints(expr const & e1, expr const & e2) {
    expr e1_fn = get_app_fn(e1);
    expr e2_fn = get_app_fn(e2);
    if (is_constant(e1_fn) && is_constant(e2_fn)) {
        buffer<unification_hint> hints;
        get_unification_hints(m_env, const_name(e1_fn), const_name(e2_fn), hints);
        for (unification_hint const & hint : hints) {
            scope s(*this);
            lean_trace(name({"old_type_context", "unification_hint"}),
                       tout() << e1 << " =?= " << e2
                       << ", pattern: " << hint.get_lhs() << " =?= " << hint.get_rhs() << "\n";);
            if (unification_hint_fn(*this, hint)(e1, e2)) {
                s.commit();
                return true;
            }
        }
    }
    return false;
}

*/

bool type_context::is_def_eq(expr const & e1, expr const & e2) {
    return false;
}

bool type_context::relaxed_is_def_eq(expr const & e1, expr const & e2) {
    flet<transparency_mode> set(m_transparency_mode, transparency_mode::All);
    return is_def_eq(e1, e2);
}
}
