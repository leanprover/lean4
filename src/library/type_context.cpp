/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/flet.h"
#include "util/interrupt.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/replace_fn.h"
#include "kernel/for_each_fn.h"
#include "kernel/inductive/inductive.h"
#include "library/trace.h"
#include "library/class.h"
#include "library/pp_options.h"
#include "library/idx_metavar.h"
#include "library/reducible.h"
#include "library/constants.h"
#include "library/metavar_util.h"
#include "library/type_context.h"
#include "library/aux_recursors.h"
#include "library/unification_hint.h"

#ifndef LEAN_DEFAULT_CLASS_INSTANCE_MAX_DEPTH
#define LEAN_DEFAULT_CLASS_INSTANCE_MAX_DEPTH 32
#endif

#ifndef LEAN_DEFAULT_CLASS_TRANS_INSTANCES
#define LEAN_DEFAULT_CLASS_TRANS_INSTANCES true
#endif

namespace lean {
static name * g_class_instance_max_depth     = nullptr;
static name * g_class_trans_instances        = nullptr;

unsigned get_class_instance_max_depth(options const & o) {
    return o.get_unsigned(*g_class_instance_max_depth, LEAN_DEFAULT_CLASS_INSTANCE_MAX_DEPTH);
}

bool get_class_trans_instances(options const & o) {
    return o.get_bool(*g_class_trans_instances, LEAN_DEFAULT_CLASS_TRANS_INSTANCES);
}

/* =====================
   type_context_cache
   ===================== */

type_context_cache::type_context_cache(environment const & env, options const & opts):
    m_env(env),
    m_options(opts),
    m_proj_info(get_projection_info_map(env)),
    m_frozen_mode(false),
    m_local_instances_initialized(false) {
    m_ci_max_depth       = get_class_instance_max_depth(opts);
    m_ci_trans_instances = get_class_trans_instances(opts);
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

static void collect_local_decls(expr const & e, buffer<name> & r, name_set & s) {
    for_each(e, [&](expr const & e, unsigned) {
            if (is_local_decl_ref(e)) {
                name const & n = mlocal_name(e);
                if (!s.contains(n)) {
                    r.push_back(n);
                    s.insert(n);
                }
            }
            return true;
        });
}

local_context type_context_cache::freeze_local_instances(metavar_context & mctx, local_context const & lctx) {
    lean_assert(!m_frozen_mode);
    type_context ctx(mctx, lctx, *this);
    m_instance_cache.clear();
    m_subsingleton_cache.clear();
    m_local_instances.clear();
    buffer<name> to_freeze;
    name_set to_freeze_set;
    lctx.for_each([&](local_decl const & decl) {
            if (auto cls_name = ctx.is_class(decl.get_type())) {
                m_local_instances.emplace_back(*cls_name, decl.mk_ref());
                to_freeze.push_back(decl.get_name());
                to_freeze_set.insert(decl.get_name());
            }
        });
    local_context new_lctx = lctx;
    for (unsigned i = 0; i < to_freeze.size(); i++) {
        new_lctx.freeze(to_freeze[i]);
        /* freeze dependencies */
        if (auto decl = lctx.get_local_decl(to_freeze[i])) {
            collect_local_decls(decl->get_type(), to_freeze, to_freeze_set);
            if (auto v = decl->get_value())
                collect_local_decls(*v, to_freeze, to_freeze_set);
        }
    }
    m_frozen_mode = true;
    return new_lctx;
}

type_context_cache::scope_pos_info::scope_pos_info(type_context_cache & o, pos_info_provider const * pip,
                                                   expr const & pos_ref):
    m_owner(o),
    m_old_pip(m_owner.m_pip),
    m_old_pos(m_owner.m_ci_pos) {
    m_owner.m_pip = pip;
    if (pip)
        m_owner.m_ci_pos = pip->get_pos_info(pos_ref);
}

type_context_cache::scope_pos_info::~scope_pos_info() {
    m_owner.m_pip    = m_old_pip;
    m_owner.m_ci_pos = m_old_pos;
}

/* =====================
   type_context::tmp_locals
   ===================== */
type_context::tmp_locals::~tmp_locals() {
    for (unsigned i = 0; i < m_locals.size(); i++)
        m_ctx.pop_local();
}

bool type_context::tmp_locals::all_let_decls() const {
    for (expr const & l : m_locals) {
        if (optional<local_decl> d = m_ctx.m_lctx.get_local_decl(l)) {
            if (!d->get_value())
                return false;
        } else {
            lean_unreachable();
        }
    }
    return true;
}

/* =====================
   type_context
   ===================== */

void type_context::init_core(transparency_mode m) {
    m_used_assignment             = false;
    m_transparency_mode           = m;
    m_in_is_def_eq                = false;
    m_is_def_eq_depth             = 0;
    m_tmp_uassignment             = nullptr;
    m_tmp_eassignment             = nullptr;
    m_cache.m_init_local_context = m_lctx;
    if (!m_cache.m_frozen_mode) {
        /* default type class resolution mode */
        m_cache.m_local_instances_initialized = false;
    }
    m_unfold_pred                 = nullptr;
}

type_context::type_context(metavar_context & mctx, local_context const & lctx, type_context_cache & cache,
                           transparency_mode m):
    m_mctx(mctx), m_lctx(lctx), m_cache(cache) {
    init_core(m);
}

type_context::~type_context() {
}

expr type_context::push_local(name const & pp_name, expr const & type, binder_info const & bi) {
    return m_lctx.mk_local_decl(pp_name, type, bi);
}

void type_context::pop_local() {
    return m_lctx.pop_local_decl();
}

pair<local_context, expr> type_context::revert_core(buffer<expr> & to_revert, local_context const & ctx,
                                                    expr const & type) {
    DEBUG_CODE({
            for (unsigned i = 0; i < to_revert.size(); i++) {
                lean_assert(is_local_decl_ref(to_revert[i]));
                optional<local_decl> const & decl = ctx.get_local_decl(to_revert[i]);
                lean_assert(decl);
                if (i > 1) {
                    optional<local_decl> const & prev_decl = ctx.get_local_decl(to_revert[i-1]);
                    lean_assert(prev_decl && prev_decl->get_idx() < decl->get_idx());
                }
            }
        });
    unsigned num   = to_revert.size();
    if (num == 0) {
        return mk_pair(ctx, type);
    }
    local_decl d0  = *ctx.get_local_decl(to_revert[0]);
    unsigned next_idx = 1;
    ctx.for_each_after(d0, [&](local_decl const & d) {
            /* Check if d is in initial to_revert */
            for (unsigned i = next_idx; i < num; i++) {
                if (mlocal_name(to_revert[i]) == d.get_name()) {
                    next_idx++;
                    return;
                }
            }
            /* We may still need to revert d if it depends on locals already in reverted */
            if (depends_on(d, to_revert)) {
                to_revert.push_back(d.mk_ref());
            }
        });
    local_context new_ctx = ctx.remove(to_revert);
    return mk_pair(new_ctx, mk_pi(to_revert, type));
}

expr type_context::revert_core(buffer<expr> & to_revert, expr const & mvar) {
    lean_assert(is_metavar_decl_ref(mvar));
    metavar_decl const & d = *m_mctx.get_metavar_decl(mvar);
    auto p = revert_core(to_revert, d.get_context(), d.get_type());
    return m_mctx.mk_metavar_decl(p.first, p.second);
}

expr type_context::revert(buffer<expr> & to_revert, expr const & mvar) {
    lean_assert(is_metavar_decl_ref(mvar));
    lean_assert(std::all_of(to_revert.begin(), to_revert.end(), [&](expr const & l) {
                return static_cast<bool>(m_mctx.get_metavar_decl(mvar)->get_context().get_local_decl(l)); }));
    expr new_mvar = revert_core(to_revert, mvar);
    expr r = new_mvar;
    for (expr const & a : to_revert) {
        if (!m_lctx.get_local_decl(a)->get_value()) {
            // 'a' is not a let-decl
            r = mk_app(r, a);
        }
    }
    m_mctx.assign(mvar, r);
    return r;
}

/* Make sure that for any (unassigned) metavariable ?M@C occurring in \c e,
   \c C does not contain any local in \c locals. This can be achieved by creating new metavariables
   ?M'@C' where C' is C without any locals (and its dependencies) */
void type_context::restrict_metavars_context(expr const & e, unsigned num_locals, expr const * locals) {
    if (!has_expr_metavar(e))
        return;
    for_each(e, [&](expr const & e, unsigned) {
            if (!has_expr_metavar(e)) return false;
            if (is_metavar_decl_ref(e)) {
                metavar_decl const & decl  = *m_mctx.get_metavar_decl(e);
                restrict_metavars_context(decl.get_type(), num_locals, locals);
                if (optional<expr> v = m_mctx.get_assignment(e)) {
                    restrict_metavars_context(*v, num_locals, locals);
                } else {
                    local_context const &  ctx = decl.get_context();
                    buffer<expr> to_revert;
                    for (unsigned i = 0; i < num_locals; i++) {
                        if (ctx.get_local_decl(locals[i]))
                            to_revert.push_back(locals[i]);
                    }
                    if (!to_revert.empty()) {
                        revert(to_revert, e);
                        lean_assert(m_mctx.is_assigned(e));
                    }
                }
            }
            return true;
        });
}

void type_context::restrict_metavars_context(local_decl const & d, unsigned num_locals, expr const * locals) {
    restrict_metavars_context(d.get_type(), num_locals, locals);
    if (auto v = d.get_value())
        restrict_metavars_context(*v, num_locals, locals);
}

expr type_context::abstract_locals(expr const & e, unsigned num_locals, expr const * locals) {
    lean_assert(std::all_of(locals, locals+num_locals, is_local_decl_ref));
    if (num_locals == 0)
        return e;
    if (!in_tmp_mode()) {
        /* In regular mode, we have to make sure the context of the metavariables occurring \c e
           does not include the locals being abstracted.

           Claim: this check is not necessary in tmp_mode because
           1- Regular metavariables should not depend on temporary local constants that have been created in tmp mode.
           2- The tmp metavariables all share the same fixed local context.
        */
        restrict_metavars_context(e, num_locals, locals);
    }
    return ::lean::abstract_locals(e, num_locals, locals);
}

expr type_context::mk_binding(bool is_pi, unsigned num_locals, expr const * locals, expr const & e) {
    buffer<local_decl>     decls;
    buffer<expr>           types;
    buffer<optional<expr>> values;
    for (unsigned i = 0; i < num_locals; i++) {
        local_decl const & decl = *m_lctx.get_local_decl(locals[i]);
        decls.push_back(decl);
        types.push_back(abstract_locals(decl.get_type(), i, locals));
        if (auto v = decl.get_value())
            values.push_back(some_expr(abstract_locals(*v, i, locals)));
        else
            values.push_back(none_expr());
    }
    expr new_e = abstract_locals(e, num_locals, locals);
    lean_assert(types.size() == values.size());
    unsigned i = types.size();
    while (i > 0) {
        --i;
        if (values[i]) {
            new_e = mk_let(decls[i].get_pp_name(), types[i], *values[i], new_e);
        } else if (is_pi) {
            new_e = ::lean::mk_pi(decls[i].get_pp_name(), types[i], new_e, decls[i].get_info());
        } else {
            new_e = ::lean::mk_lambda(decls[i].get_pp_name(), types[i], new_e, decls[i].get_info());
        }
    }
    return new_e;
}

expr type_context::mk_lambda(buffer<expr> const & locals, expr const & e) {
    return mk_binding(false, locals.size(), locals.data(), e);
}

expr type_context::mk_pi(buffer<expr> const & locals, expr const & e) {
    return mk_binding(true, locals.size(), locals.data(), e);
}

expr type_context::mk_lambda(expr const & local, expr const & e) {
    return mk_binding(false, 1, &local, e);
}

expr type_context::mk_pi(expr const & local, expr const & e) {
    return mk_binding(true, 1, &local, e);
}

expr type_context::mk_lambda(std::initializer_list<expr> const & locals, expr const & e) {
    return mk_binding(false, locals.size(), locals.begin(), e);
}

expr type_context::mk_pi(std::initializer_list<expr> const & locals, expr const & e) {
    return mk_binding(true, locals.size(), locals.begin(), e);
}

/* ---------------------
   Normalization
   -------------------- */

optional<declaration> type_context::is_transparent(transparency_mode m, name const & n) {
    return m_cache.is_transparent(m, n);
}

optional<declaration> type_context::is_transparent(name const & n) {
    return is_transparent(m_transparency_mode, n);
}

/* Unfold \c e if it is a constant */
optional<expr> type_context::unfold_definition_core(expr const & e) {
    if (is_constant(e)) {
        if (auto d = is_transparent(const_name(e))) {
            if (length(const_levels(e)) == d->get_num_univ_params())
                return some_expr(instantiate_value_univ_params(*d, const_levels(e)));
        }
    }
    return none_expr();
}

/* Unfold head(e) if it is a constant */
optional<expr> type_context::unfold_definition(expr const & e) {
    if (is_app(e)) {
        expr f0 = get_app_fn(e);
        if (auto f  = unfold_definition_core(f0)) {
            buffer<expr> args;
            get_app_rev_args(e, args);
            return some_expr(apply_beta(*f, args.size(), args.data()));
        } else {
            return none_expr();
        }
    } else {
        return unfold_definition_core(e);
    }
}

optional<expr> type_context::try_unfold_definition(expr const & e) {
    if (m_unfold_pred && !(*m_unfold_pred)(e))
        return none_expr();
    return unfold_definition(e);
}

optional<expr> type_context::reduce_projection(expr const & e) {
    expr const & f = get_app_fn(e);
    if (!is_constant(f))
        return none_expr();
    projection_info const * info = m_cache.m_proj_info.find(const_name(f));
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

optional<expr> type_context::reduce_aux_recursor(expr const & e) {
    expr const & f = get_app_fn(e);
    if (!is_constant(f))
        return none_expr();
    if (is_aux_recursor(env(), const_name(f)))
        return try_unfold_definition(e);
    else
        return none_expr();
}

bool type_context::should_unfold_macro(expr const & e) {
    /* If m_transparency_mode is set to ALL, then we unfold all
       macros. In this way, we make sure type inference does not fail.
       We also unfold macros when reducing inside of is_def_eq. */
    return
        m_transparency_mode == transparency_mode::All ||
        m_in_is_def_eq ||
        m_cache.should_unfold_macro(e);
}

optional<expr> type_context::expand_macro(expr const & e) {
    lean_assert(is_macro(e));
    if (should_unfold_macro(e)) {
        return macro_def(e).expand(e, *this);
    } else {
        return none_expr();
    }
}

/*
  Apply beta-reduction, zeta-reduction (i.e., unfold let local-decls), iota-reduction,
  unfold macros, expand let-expressions, expand assigned meta-variables.

  This method does *not* apply delta-reduction at the head.
  Reason: we want to perform these reductions lazily at is_def_eq.

  Remark: this method delta-reduce (transparent) aux-recursors (e.g., cases_on, rec_on).
*/
expr type_context::whnf_core(expr const & e) {
    switch (e.kind()) {
    case expr_kind::Var:      case expr_kind::Sort:
    case expr_kind::Pi:       case expr_kind::Lambda:
    case expr_kind::Constant:
        /* Remark: we do not unfold Constants eagerly in this method */
        return e;
    case expr_kind::Local:
        if (auto d = m_lctx.get_local_decl(e)) {
            if (auto v = d->get_value()) {
                /* zeta-reduction */
                return whnf_core(*v);
            }
        }
        return e;
    case expr_kind::Meta:
        if (is_metavar_decl_ref(e)) {
            if (m_mctx.is_assigned(e)) {
                m_used_assignment = true;
                return m_mctx.instantiate_mvars(e);
            }
        } else if (is_idx_metavar(e)) {
            unsigned idx = to_meta_idx(e);
            if (idx < m_tmp_eassignment->size()) {
                if (auto v = (*m_tmp_eassignment)[idx]) {
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
            /* beta-reduction */
            unsigned m = 1;
            unsigned num_args = args.size();
            while (is_lambda(binding_body(f)) && m < num_args) {
                f = binding_body(f);
                m++;
            }
            lean_assert(m <= num_args);
            return whnf_core(mk_rev_app(::lean::instantiate(binding_body(f), m, args.data() + (num_args - m)),
                                        num_args - m, args.data()));
        } else if (f == f0) {
            if (auto r = norm_ext(e)) {
                /* mainly iota-reduction, it also applies HIT and quotient reduction rules */
                return whnf_core(*r);
            } else if (auto r = reduce_projection(e)) {
                return whnf_core(*r);
            } else if (auto r = reduce_aux_recursor(e)) {
                return whnf_core(*r);
            } else {
                return e;
            }
        } else {
            return whnf_core(mk_rev_app(f, args.size(), args.data()));
        }
    }}
    lean_unreachable();
}

expr type_context::whnf(expr const & e) {
    expr t = e;
    while (true) {
        expr t1 = whnf_core(t);
        if (auto next_t = unfold_definition(t1)) {
            t = *next_t;
        } else {
            return t1;
        }
    }
}

expr type_context::whnf_pred(expr const & e, std::function<bool(expr const &)> const & pred) { // NOLINT
    flet<std::function<bool(expr const &)> const *>set_unfold_pred(m_unfold_pred, &pred); // NOLINT
    expr t = e;
    while (true) {
        expr t1 = whnf_core(t);
        if (auto next_t = try_unfold_definition(t1)) {
            t = *next_t;
        } else {
            return t1;
        }
    }
}

expr type_context::relaxed_whnf(expr const & e) {
    flet<transparency_mode> set(m_transparency_mode, transparency_mode::All);
    return whnf(e);
}

optional<expr> type_context::is_stuck(expr const &) {
    // TODO(Leo): check whether we need this method after refactoring
    return none_expr();
}

expr type_context::try_to_pi(expr const & e) {
    expr new_e = whnf(e);
    if (is_pi(new_e))
        return new_e;
    else
        return e;
}

expr type_context::relaxed_try_to_pi(expr const & e) {
    flet<transparency_mode> set(m_transparency_mode, transparency_mode::All);
    return try_to_pi(e);
}

/* ---------------
   Type inference
   --------------- */

expr type_context::infer(expr const & e) {
    flet<transparency_mode> set(m_transparency_mode, transparency_mode::All);
    return infer_core(e);
}

expr type_context::infer_core(expr const & e) {
    lean_assert(!is_var(e));
    lean_assert(closed(e));

    auto & cache = m_cache.m_infer_cache;
    auto it = cache.find(e);
    if (it != cache.end())
        return it->second;

    reset_used_assignment reset(*this);

    expr r;
    switch (e.kind()) {
    case expr_kind::Local:
        r = infer_local(e);
        break;
    case expr_kind::Meta:
        r = infer_metavar(e);
        break;
    case expr_kind::Var:
        lean_unreachable();  // LCOV_EXCL_LINE
    case expr_kind::Sort:
        r = mk_sort(mk_succ(sort_level(e)));
        break;
    case expr_kind::Constant:
        r = infer_constant(e);
        break;
    case expr_kind::Macro:
        r = infer_macro(e);
        break;
    case expr_kind::Lambda:
        r = infer_lambda(e);
        break;
    case expr_kind::Pi:
        r = infer_pi(e);
        break;
    case expr_kind::App:
        r = infer_app(e);
        break;
    case expr_kind::Let:
        r = infer_let(e);
        break;
    }

    if (!m_used_assignment)
        cache.insert(mk_pair(e, r));
    return r;
}

expr type_context::infer_local(expr const & e) {
    lean_assert(is_local(e));
    if (is_local_decl_ref(e)) {
        auto d = m_lctx.get_local_decl(e);
        if (!d)
            throw exception("infer type failed, unknown variable");
        lean_assert(d);
        return d->get_type();
    } else {
        /* Remark: depending on how we re-organize the parser, we may be able
           to remove this branch. */
        return mlocal_type(e);
    }
}

expr type_context::infer_metavar(expr const & e) {
    if (is_metavar_decl_ref(e)) {
        auto d = m_mctx.get_metavar_decl(e);
        if (!d)
            throw exception("infer type failed, unknown metavariable");
        return d->get_type();
    } else {
        /* tmp metavariables should only occur in tmp_mode */
        lean_assert(!is_idx_metavar(e) || in_tmp_mode());
        return mlocal_type(e);
    }
}

expr type_context::infer_constant(expr const & e) {
    declaration d   = env().get(const_name(e));
    auto const & ps = d.get_univ_params();
    auto const & ls = const_levels(e);
    if (length(ps) != length(ls))
        throw exception("infer type failed, incorrect number of universe levels");
    return instantiate_type_univ_params(d, ls);
}

expr type_context::infer_macro(expr const & e) {
    auto def = macro_def(e);
    bool infer_only = true;
    return def.check_type(e, *this, infer_only);
}

expr type_context::infer_lambda(expr e) {
    buffer<expr> es, ds;
    tmp_locals ls(*this);
    while (is_lambda(e)) {
        es.push_back(e);
        ds.push_back(binding_domain(e));
        expr d = instantiate_rev(binding_domain(e), ls.size(), ls.data());
        expr l = ls.push_local(binding_name(e), d, binding_info(e));
        e = binding_body(e);
    }
    check_system("infer_type");
    expr t = infer_core(instantiate_rev(e, ls.size(), ls.data()));
    expr r = abstract_locals(t, ls.size(), ls.data());
    unsigned i = es.size();
    while (i > 0) {
        --i;
        r = ::lean::mk_pi(binding_name(es[i]), ds[i], r, binding_info(es[i]));
    }
    return r;
}

optional<level> type_context::get_level_core(expr const & A) {
    lean_assert(m_transparency_mode == transparency_mode::All);
    expr A_type = whnf(infer_core(A));
    while (true) {
        if (is_sort(A_type)) {
            return some_level(sort_level(A_type));
        } else if (is_mvar(A_type)) {
            if (auto v = get_assignment(A_type)) {
                A_type = *v;
            } else if (!in_tmp_mode() && is_metavar_decl_ref(A_type)) {
                /* We should only assign A_type IF we are not in tmp mode. */
                level r = m_mctx.mk_univ_metavar_decl();
                assign(A_type, mk_sort(r));
                return some_level(r);
            } else if (in_tmp_mode() && is_idx_metavar(A_type)) {
                level r = mk_tmp_univ_mvar();
                assign(A_type, mk_sort(r));
                return some_level(r);
            } else {
                return none_level();
            }
        } else {
            return none_level();
        }
    }
}

level type_context::get_level(expr const & A) {
    if (auto r = get_level_core(A)) {
        return *r;
    } else {
        throw exception("infer type failed, sort expected");
    }
}

expr type_context::infer_pi(expr e) {
    tmp_locals ls(*this);
    buffer<level> us;
    while (is_pi(e)) {
        expr d  = instantiate_rev(binding_domain(e), ls.size(), ls.data());
        us.push_back(get_level(d));
        expr l  = ls.push_local(binding_name(e), d, binding_info(e));
        e = binding_body(e);
    }
    e = instantiate_rev(e, ls.size(), ls.data());
    level r = get_level(e);
    unsigned i = ls.size();
    bool imp = env().impredicative();
    while (i > 0) {
        --i;
        r = imp ? mk_imax(us[i], r) : mk_max(us[i], r);
    }
    return mk_sort(r);
}

expr type_context::infer_app(expr const & e) {
    check_system("infer_type");
    buffer<expr> args;
    expr const & f = get_app_args(e, args);
    expr f_type    = infer_core(f);
    unsigned j     = 0;
    unsigned nargs = args.size();
    for (unsigned i = 0; i < nargs; i++) {
        if (is_pi(f_type)) {
            f_type = binding_body(f_type);
        } else {
            lean_assert(m_transparency_mode == transparency_mode::All);
            f_type = whnf(instantiate_rev(f_type, i-j, args.data()+j));
            if (!is_pi(f_type))
                throw exception("infer type failed, Pi expected");
            f_type = binding_body(f_type);
            j = i;
        }
    }
    return instantiate_rev(f_type, nargs-j, args.data()+j);
}

expr type_context::infer_let(expr e) {
    /*
      We may also infer the type of a let-expression by using
      tmp_locals, push_let, and they closing the resulting type with
      let-expressions.
      It is unclear which option is the best / more efficient.
      The following implementation doesn't need the extra step,
      but it relies on the cache to avoid repeated work.
    */
    buffer<expr> vs;
    while (is_let(e)) {
        expr v = instantiate_rev(let_value(e), vs.size(), vs.data());
        vs.push_back(v);
        e = let_body(e);
    }
    check_system("infer_type");
    return infer_core(instantiate_rev(e, vs.size(), vs.data()));
}

expr type_context::check(expr const & e) {
    // TODO(Leo): infer doesn't really check anything
    return infer(e);
}

bool type_context::is_prop(expr const & e) {
    if (env().impredicative()) {
        expr t = whnf(infer(e));
        return t == mk_Prop();
    } else {
        return false;
    }
}

/* -------------------------------
   Temporary assignment mode support
   ------------------------------- */
void type_context::set_tmp_mode(buffer<optional<level>> & tmp_uassignment, buffer<optional<expr>> & tmp_eassignment) {
    lean_assert(!in_tmp_mode());
    lean_assert(m_scopes.empty());
    lean_assert(m_tmp_trail.empty());
    m_tmp_mvar_lctx = m_lctx;
    m_tmp_uassignment = &tmp_uassignment;
    m_tmp_eassignment = &tmp_eassignment;
}

void type_context::reset_tmp_mode() {
    lean_assert(m_scopes.empty());
    m_tmp_trail.clear();
    m_tmp_uassignment = nullptr;
    m_tmp_eassignment = nullptr;
}

void type_context::ensure_num_tmp_mvars(unsigned num_uvars, unsigned num_mvars) {
    lean_assert(in_tmp_mode());
    if (m_tmp_uassignment->size() < num_uvars)
        m_tmp_uassignment->resize(num_uvars, none_level());
    if (m_tmp_eassignment->size() < num_mvars)
        m_tmp_eassignment->resize(num_mvars, none_expr());
}

optional<level> type_context::get_tmp_uvar_assignment(unsigned idx) const {
    lean_assert(in_tmp_mode());
    lean_assert(idx < m_tmp_uassignment->size());
    return (*m_tmp_uassignment)[idx];
}

optional<expr> type_context::get_tmp_mvar_assignment(unsigned idx) const {
    lean_assert(in_tmp_mode());
    lean_assert(idx < m_tmp_eassignment->size());
    return (*m_tmp_eassignment)[idx];
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
    lean_assert(in_tmp_mode());
    lean_assert(is_idx_metauniv(u));
    lean_assert(to_meta_idx(u) < m_tmp_uassignment->size());
    unsigned idx = to_meta_idx(u);
    if (!m_scopes.empty() && !(*m_tmp_uassignment)[idx]) {
        m_tmp_trail.emplace_back(tmp_trail_kind::Level, idx);
    }
    (*m_tmp_uassignment)[idx] = l;
}

void type_context::assign_tmp(expr const & m, expr const & v) {
    lean_assert(in_tmp_mode());
    lean_assert(is_idx_metavar(m));
    lean_assert(to_meta_idx(m) < m_tmp_eassignment->size());
    unsigned idx = to_meta_idx(m);
    if (!m_scopes.empty() && !(*m_tmp_eassignment)[idx]) {
        m_tmp_trail.emplace_back(tmp_trail_kind::Expr, idx);
    }
    (*m_tmp_eassignment)[to_meta_idx(m)] = v;
}

level type_context::mk_tmp_univ_mvar() {
    lean_assert(in_tmp_mode());
    unsigned idx = m_tmp_uassignment->size();
    m_tmp_uassignment->push_back(none_level());
    return mk_idx_metauniv(idx);
}

expr type_context::mk_tmp_mvar(expr const & type) {
    lean_assert(in_tmp_mode());
    unsigned idx = m_tmp_eassignment->size();
    m_tmp_eassignment->push_back(none_expr());
    return mk_idx_metavar(idx, type);
}

/* -----------------------------------
   Uniform interface to temporary & regular metavariables
   ----------------------------------- */

bool type_context::is_mvar(level const & l) const {
    if (in_tmp_mode())
        return is_idx_metauniv(l);
    else
        return is_metavar_decl_ref(l);
}

bool type_context::is_mvar(expr const & e) const {
    if (in_tmp_mode())
        return is_idx_metavar(e);
    else
        return is_metavar_decl_ref(e);
}

bool type_context::is_assigned(level const & l) const {
    const_cast<type_context*>(this)->m_used_assignment = true;
    if (in_tmp_mode())
        return static_cast<bool>(get_tmp_assignment(l));
    else
        return m_mctx.is_assigned(l);
}

bool type_context::is_assigned(expr const & e) const {
    const_cast<type_context*>(this)->m_used_assignment = true;
    if (in_tmp_mode())
        return static_cast<bool>(get_tmp_assignment(e));
    else
        return m_mctx.is_assigned(e);
}

optional<level> type_context::get_assignment(level const & l) const {
    const_cast<type_context*>(this)->m_used_assignment = true;
    if (in_tmp_mode())
        return get_tmp_assignment(l);
    else
        return m_mctx.get_assignment(l);
}

optional<expr> type_context::get_assignment(expr const & e) const {
    const_cast<type_context*>(this)->m_used_assignment = true;
    if (in_tmp_mode())
        return get_tmp_assignment(e);
    else
        return m_mctx.get_assignment(e);
}

void type_context::assign(level const & u, level const & l) {
    m_used_assignment = true;
    if (in_tmp_mode())
        assign_tmp(u, l);
    else
        m_mctx.assign(u, l);
}

void type_context::assign(expr const & m, expr const & v) {
    m_used_assignment = true;
    if (in_tmp_mode())
        assign_tmp(m, v);
    else
        m_mctx.assign(m, v);
}

level type_context::instantiate_mvars(level const & l) {
    return ::lean::instantiate_mvars(*this, l);
}

expr type_context::instantiate_mvars(expr const & e) {
    return ::lean::instantiate_mvars(*this, e);
}

/* -----------------------------------
   Backtracking
   ----------------------------------- */

void type_context::push_scope() {
    if (in_tmp_mode()) {
        m_scopes.emplace_back(m_mctx, m_tmp_uassignment->size(), m_tmp_eassignment->size(), m_tmp_trail.size());
    } else {
        m_scopes.emplace_back(m_mctx, 0, 0, 0);
    }
}

void type_context::pop_scope() {
    lean_assert(!m_scopes.empty());
    scope_data const & s = m_scopes.back();
    m_mctx = s.m_mctx;
    if (in_tmp_mode()) {
        unsigned old_sz = s.m_tmp_trail_sz;
        while (m_tmp_trail.size() > old_sz) {
            auto const & t = m_tmp_trail.back();
            if (t.first == tmp_trail_kind::Level) {
                (*m_tmp_uassignment)[t.second] = none_level();
            } else {
                (*m_tmp_eassignment)[t.second] = none_expr();
            }
            m_tmp_trail.pop_back();
        }
        lean_assert(old_sz == m_tmp_trail.size());
        m_tmp_uassignment->shrink(s.m_tmp_uassignment_sz);
        m_tmp_eassignment->shrink(s.m_tmp_eassignment_sz);
    }
    m_scopes.pop_back();
}

void type_context::commit_scope() {
    lean_assert(!m_scopes.empty());
    m_scopes.pop_back();
}

/* -----------------------------------
   Unification / definitional equality
   ----------------------------------- */

bool type_context::is_def_eq(level const & l1, level const & l2) {
    if (is_equivalent(l1, l2)) {
        return true;
    }

    if (is_mvar(l1)) {
        if (auto v = get_assignment(l1)) {
            return is_def_eq(*v, l2);
        } else {
            assign(l1, l2);
            return true;
        }
    }

    if (is_mvar(l2)) {
        if (auto v = get_assignment(l2)) {
            return is_def_eq(l1, *v);
        } else {
            assign(l2, l1);
            return true;
        }
    }

    level new_l1 = normalize(instantiate_mvars(l1));
    level new_l2 = normalize(instantiate_mvars(l2));

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

bool type_context::approximate() {
    // TODO(Leo): add flag at type_context_cache to force approximated mode.
    return in_tmp_mode();
}

/* If \c e is a let local-decl, then unfold it, otherwise return e. */
expr type_context::try_zeta(expr const & e) {
    if (!is_local_decl_ref(e))
        return e;
    if (auto d = m_lctx.get_local_decl(e)) {
        if (auto v = d->get_value())
            return *v;
    }
    return e;
}

expr type_context::expand_let_decls(expr const & e) {
    return replace(e, [&](expr const & e, unsigned) {
            if (is_local_decl_ref(e)) {
                if (auto d = m_lctx.get_local_decl(e)) {
                    if (auto v = d->get_value())
                        return some_expr(*v);
                }
            }
            return none_expr();
        });
}

/*
We declare metavariables with respect to a local context.
We use the notation (`?M@C`) to denote a metavariable `?M` that was defined at local context `C`.
Remark: for temporary metavariables, the variable m_tmp_mvar_lctx stores their context.

The following method process the unification constraint

       ?M@C a_1 ... a_n =?= t

We say the unification constraint is a pattern IFF

    1) `a_1 ... a_n` are pairwise distinct local constants that are ​*not*​ references to let-decls.
    2) `a_1 ... a_n` have ​*not*​ been defined in `C`
    3) `t` only contains local constants in `C` and/or `{a_1, ..., a_n}`
    4) For every metavariable `?M'@C'` occurring in `t`, `C'` is a subset of `C`
    5) `?M` does not occur in `t`

Claim: we don't have to check local declaration definitions. That is,
if `t` contains a reference to `x : A := v`, we don't need to check `v`.
Reason: The reference to `x` is a local constant, and it must be in `C` (by 1 and 3).
If `x` is in `C`, then any metavariable occurring in `v` must have been defined in a strict subset of `C`.
So, condition 4 and 5 are satisfied.

If the conditions above have been satisfied, then the
solution for the unification constrain is

   ?M := fun a_1 ... a_n, t

Now, we consider some workarounds/approximations.

 A1) Suppose `t` contains a reference to `x : A := v` and `x` is not in `C` (failed condition 3)
     (precise) solution: unfold `x` in `t`.

 A2) Suppose some `a_i` is in `C` (failed condition 2)
     (approximated) solution (when approximate() predicate returns true) :
     ignore condition and also use

        ?M := fun a_1 ... a_n, t

   Here is an example where this approximation fails:
   Given `C` containing `a : nat`, consider the following two constraints
         ?M@C a =?= a
         ?M@C b =?= a

   If we use the approximation in the first constraint, we get
         ?M := fun x, x
   when we apply this solution to the second one we get a failure.

 A3) `a_1 ... a_n` are not pairwise distinct (failed condition 1).
   We can approximate again, but the limitations are very similar to the previous one.

 A4) `t` contains a metavariable `?M'@C'` where `C'` is not a subset of `C`.
   (approximated) solution: restrict the context of `?M'`
   If `?M'` is assigned, the workaround is precise, and we just unfold `?M'`.

   Remark: we only implement the ?M' assigned case.

 A5) If some `a_i` is not a local constant,
     then we use first-order unification (if approximate() is true)

       ?M a_1 ... a_i a_{i+1} ... a_{i+k} =?= f b_1 ... b_k

   reduces to

       ?M a_1 ... a_i =?= f
       a_{i+1}        =?= b_1
       ...
       a_{i+k}        =?= b_k
*/
bool type_context::process_assignment(expr const & m, expr const & v) {
    buffer<expr> args;
    expr const & mvar = get_app_args(m, args);
    lean_assert(is_mvar(mvar));
    optional<metavar_decl> mvar_decl;
    if (!in_tmp_mode()) {
        mvar_decl = m_mctx.get_metavar_decl(mvar);
        if (!mvar_decl) return false;
    }
    buffer<expr> locals;
    bool use_fo     = false; /* if true, we use first-order unification */
    bool add_locals = true;  /* while true we copy args to locals */
    for (unsigned i = 0; i < args.size(); i++) {
        expr arg = args[i];
        /* try to instantiate */
        if (is_meta(arg))
            arg = instantiate_mvars(arg);
        arg = try_zeta(arg); /* unfold let-constant if needed. */
        args[i] = arg;
        if (!is_local_decl_ref(arg)) {
            /* m is of the form (?M ... t ...) where t is not a local constant. */
            if (approximate()) {
                /* workaround A5 */
                use_fo     = true;
                add_locals = false;
            } else {
                return false;
            }
        } else {
            if (std::any_of(locals.begin(), locals.end(),
                            [&](expr const & local) { return mlocal_name(local) == mlocal_name(arg); })) {
                /* m is of the form (?M ... l ... l ...) where l is a local constant. */
                if (approximate()) {
                    /* workaround A3 */
                    add_locals = false;
                } else {
                    return false;
                }
            }
            /* Make sure arg is not in the context of the metavariable mvar
               The code is slightly different for tmp mode because the metavariables
               do not store their local context. */
            if (in_tmp_mode()) {
                if (m_tmp_mvar_lctx.get_local_decl(arg)) {
                    /* m is of the form (?M@C ... l ...) where l is a local constant in C */
                    if (!approximate())
                        return false;
                }
            } else {
                if (mvar_decl->get_context().get_local_decl(arg)) {
                    /* m is of the form (?M@C ... l ...) where l is a local constant in C. */
                    if (!approximate())
                        return false;
                }
            }
        }
        if (add_locals)
            locals.push_back(arg);
    }

    expr new_v = instantiate_mvars(v); /* enforce A4 */

    if (use_fo) {
        /* Use first-order unification.
           Workaround A5. */
        buffer<expr> new_v_args;
        expr new_v_fn = get_app_args(new_v, new_v_args);
        expr new_mvar = mvar;
        unsigned i = 0;
        unsigned j = 0;
        if (args.size() > new_v_args.size()) {
            /*
               ?M a_1 ... a_i a_{i+1} ... a_{i+k} =?= f b_1 ... b_k

               reduces to

               ?M a_1 ... a_i =?= f
               a_{i+1}        =?= b_1
               ...
               a_{i+k}        =?= b_k
            */
            new_mvar = mk_app(mvar, args.size() - new_v_args.size(), args.data());
            i        = new_v_args.size();
        } else if (args.size() < new_v_args.size()) {
            /*
               ?M a_1 ... a_k =?= f b_1 ... b_i b_{i+1} ... b_{i+k}

               reduces to

               ?M  =?= f b_1 ... b_i
               a_1 =?= b_{i+1}
               ...
               a_k =?= b_{i+k}
            */
            new_v_fn = mk_app(new_v_fn, new_v_args.size() - args.size(), new_v_args.data());
            j        = args.size();
        } else {
            /*
               ?M a_1 ... a_k =?= f b_1 ... b_k

               reduces to
               ?M  =?= f
               a_1 =?= b_1
               ...
               a_k =?= b_k
            */
            lean_assert(new_v_args.size() == args.size());
        }
        if (!is_def_eq_core(new_mvar, new_v_fn))
            return false;
        for (; j < new_v_args.size(); i++, j++) {
            lean_assert(i < args.size());
            if (!is_def_eq_core(args[i], new_v_args[j]))
                return false;
        }
        lean_assert(i == args.size());
        lean_assert(j == new_v_args.size());
        return true;
    }

    while (true) {
        /* We use a loop here to implement workaround A1.
           If new_v has a "bad" let local decl, we expand it and try again. */
        bool ok = true;
        bool bad_let_refs = false;
        for_each(new_v, [&](expr const & e, unsigned) {
                if (!ok)
                    return false; // stop search
                if (is_mvar(e)) {
                    if (mvar == e) {
                        /* mvar occurs in v */
                        ok = false;
                        return false;
                    }
                    if (!in_tmp_mode()) {
                        /* Recall that in tmp_mode all metavariables have the same local context.
                           So, we don't need to check anything.
                           In regular mode, we need to check condition 4

                           For every metavariable `?M'@C'` occurring in `t`, `C'` is a subset of `C`
                        */
                        optional<metavar_decl> const & e_decl = m_mctx.get_metavar_decl(e);
                        if (!e_decl || !e_decl->get_context().is_subset_of(mvar_decl->get_context())) {
                            ok = false;
                            return false;
                        }
                    }
                    return false;
                } else if (is_local_decl_ref(e)) {
                    bool in_ctx;
                    if (in_tmp_mode()) {
                        in_ctx = static_cast<bool>(m_tmp_mvar_lctx.get_local_decl(e));
                    } else {
                        in_ctx = static_cast<bool>(mvar_decl->get_context().get_local_decl(e));
                    }
                    if (!in_ctx) {
                        if (auto decl = m_lctx.get_local_decl(e)) {
                            if (decl->get_value()) {
                                /* let-decl that is not in the metavar context
                                   workaround A1 */
                                ok           = false;
                                bad_let_refs = true;
                                return false;
                            }
                        }
                        if (std::all_of(locals.begin(), locals.end(), [&](expr const & a) {
                                    return mlocal_name(a) != mlocal_name(e); })) {
                            ok = false;
                            return false;
                        }
                    }
                    return false;
                }
                return true;
            });
        if (ok) {
            break;
        } else if (bad_let_refs) {
            new_v = instantiate_mvars(expand_let_decls(new_v));
        } else {
            return false;
        }
    }

    if (args.empty()) {
        /* easy case */
    } else if (args.size() == locals.size()) {
        new_v = mk_lambda(locals, new_v);
    } else {
        /*
          This case is imprecise since it is not a higher order pattern.
          That the term \c m is of the form (?M t_1 ... t_n) and the t_i's are not pairwise
          distinct local constants.
        */
        tmp_locals new_ls(*this);
        expr mvar_type = infer(mvar);
        for (unsigned i = 0; i < args.size(); i++) {
            mvar_type = relaxed_whnf(mvar_type);
            if (!is_pi(mvar_type))
                return false;
            lean_assert(i <= locals.size());
            if (i == locals.size()) {
                expr new_l = new_ls.push_local(binding_name(mvar_type), binding_domain(mvar_type));
                locals.push_back(new_l);
            }
            lean_assert(i < locals.size());
            mvar_type = ::lean::instantiate(binding_body(mvar_type), locals[i]);
        }
        lean_assert(locals.size() == args.size());
        new_v = mk_lambda(locals, new_v);
    }

    /* check types */
    try {
        expr t1 = infer(mvar);
        expr t2 = infer(new_v);
        if (!is_def_eq_core(t1, t2)) {
            lean_trace(name({"type_context", "is_def_eq_detail"}),
                       tout() << "Type mismatch when assigning " << mvar << " := " << new_v << "\n";
                       tout() << ">> " << t1 << " =?= " << t2 << "\n";);
            return false;
        }
    } catch (exception &) {
        return false;
    }

    assign(mvar, new_v);
    lean_trace(name({"type_context", "is_def_eq_detail"}), tout() << "assign: " << mvar << " := " << new_v << "\n";);
    return true;
}

bool type_context::is_def_eq_binding(expr e1, expr e2) {
    lean_assert(e1.kind() == e2.kind());
    lean_assert(is_binding(e1));
    expr_kind k = e1.kind();
    tmp_locals subst(*this);
    do {
        optional<expr> var_e1_type;
        if (binding_domain(e1) != binding_domain(e2)) {
            var_e1_type = instantiate_rev(binding_domain(e1), subst.size(), subst.data());
            expr var_e2_type = instantiate_rev(binding_domain(e2), subst.size(), subst.data());
            if (!is_def_eq_core(var_e2_type, *var_e1_type))
                return false;
        }
        if (!closed(binding_body(e1)) || !closed(binding_body(e2))) {
            // local is used inside t or s
            if (!var_e1_type)
                var_e1_type = instantiate_rev(binding_domain(e1), subst.size(), subst.data());
            subst.push_local(binding_name(e1), *var_e1_type);
        } else {
            expr const & dont_care = mk_Prop();
            subst.push_local(binding_name(e1), dont_care);
        }
        e1 = binding_body(e1);
        e2 = binding_body(e2);
    } while (e1.kind() == k && e2.kind() == k);
    return is_def_eq_core(instantiate_rev(e1, subst.size(), subst.data()),
                          instantiate_rev(e2, subst.size(), subst.data()));
}

bool type_context::is_def_eq_args(expr const & e1, expr const & e2) {
    lean_assert(is_app(e1) && is_app(e2));
    buffer<expr> args1, args2;
    get_app_args(e1, args1);
    get_app_args(e2, args2);
    if (args1.size() != args2.size())
        return false;
    for (unsigned i = 0; i < args1.size(); i++) {
        if (!is_def_eq_core(args1[i], args2[i]))
            return false;
    }
    return true;
}

/** \brief Try to solve e1 := (lambda x : A, t) =?= e2 by eta-expanding e2.

    \remark eta-reduction is not a good alternative (even in a system without cumulativity like Lean).
    Example:
         (lambda x : A, f ?M) =?= f
    The lhs cannot be eta-reduced because ?M is a meta-variable. */
bool type_context::is_def_eq_eta(expr const & e1, expr const & e2) {
    if (is_lambda(e1) && !is_lambda(e2)) {
        expr e2_type = relaxed_whnf(infer(e2));
        if (is_pi(e2_type)) {
            // e2_type may not be a Pi because it is a stuck term.
            // We are ignoring this case and just failing.
            expr new_e2 = ::lean::mk_lambda(binding_name(e2_type), binding_domain(e2_type),
                                            mk_app(e2, Var(0)), binding_info(e2_type));
            scope s(*this);
            if (is_def_eq_core(e1, new_e2)) {
                s.commit();
                return true;
            }
        }
    }
    return false;
}

bool type_context::is_def_eq_proof_irrel(expr const & e1, expr const & e2) {
    if (!env().prop_proof_irrel())
        return false;
    expr e1_type = infer(e1);
    if (is_prop(e1_type)) {
        expr e2_type = infer(e2);
        scope s(*this);
        if (is_def_eq_core(e1_type, e2_type)) {
            s.commit();
            return true;
        }
    }
    return false;
}

lbool type_context::quick_is_def_eq(expr const & e1, expr const & e2) {
    if (e1 == e2)
        return l_true;

    expr const & f1 = get_app_fn(e1);
    if (is_mvar(f1)) {
        if (is_assigned(f1)) {
            return to_lbool(is_def_eq_core(instantiate_mvars(e1), e2));
        } else {
            return to_lbool(process_assignment(e1, e2));
        }
    }

    expr const & f2 = get_app_fn(e2);
    if (is_mvar(f2)) {
        if (is_assigned(f2)) {
            return to_lbool(is_def_eq_core(e1, instantiate_mvars(e2)));
        } else {
            return to_lbool(process_assignment(e2, e1));
        }
    }

    if (e1.kind() == e2.kind()) {
        switch (e1.kind()) {
        case expr_kind::Lambda: case expr_kind::Pi:
            return to_lbool(is_def_eq_binding(e1, e2));
        case expr_kind::Sort:
            return to_lbool(is_def_eq(sort_level(e1), sort_level(e2)));
        case expr_kind::Meta:     case expr_kind::Var:
        case expr_kind::Local:    case expr_kind::App:
        case expr_kind::Constant: case expr_kind::Macro:
        case expr_kind::Let:
            // We do not handle these cases in this method.
            break;
        }
    }
    return l_undef; // This is not an "easy case"
}

/* We say a reduction is productive iff the result is not a recursor application */
bool type_context::is_productive(expr const & e) {
    /* TODO(Leo): make this more general.
       Right now we consider the following cases to be non-productive
       1)  (C.rec ...)   where rec is rec/rec_on/cases_on/brec_on
       2)  (prod.pr1 A B (C.rec ...) ...)  where rec is rec/rec_on/cases_on/brec_on

       Second case is a byproduct of the recursive equation compiler.
    */
    expr const & f = get_app_fn(e);
    if (!is_constant(f))
        return true;
    name const & n = const_name(f);
    if (n == get_prod_pr1_name()) {
        /* We use prod.pr1 when compiling recursive equations and brec_on.
           So, we should check whether the main argument of the projection
           is productive */
        buffer<expr> args;
        get_app_args(e, args);
        if (args.size() < 3)
            return false;
        expr const & major = args[2];
        return is_productive(major);
    } else {
        return !is_aux_recursor(env(), n) && !inductive::is_elim_rule(env(), n);
    }
}

expr type_context::reduce_if_productive(expr const & t) {
    if (auto r = unfold_definition(t)) {
        expr new_t = whnf_core(*r);
        if (is_productive(new_t)) {
            return new_t;
        }
    }
    return t;
}

static bool same_head_symbol(expr const & t, expr const & s) {
    expr const & f_t = get_app_fn(t);
    expr const & f_s = get_app_fn(s);
    return is_constant(f_t) && is_constant(f_s) && const_name(f_t) == const_name(f_s);
}

/* Apply unification hints and lazy delta-reduction */
lbool type_context::is_def_eq_lazy_delta(expr & t, expr & s) {
    while (true) {
        if (try_unification_hints(t, s))
            return l_true;
        auto d_t = is_delta(t);
        auto d_s = is_delta(s);
        if (!d_t && !d_s) {
            /* none of them can be delta-reduced */
            return l_undef;
        } else if (d_t && !d_s) {
            /* only t_n can be delta reduced */
            lean_trace(name({"type_context", "is_def_eq_detail"}), tout() << "unfold left: " << d_t->get_name() << "\n";);
            t = whnf_core(*unfold_definition(t));
        } else if (!d_t && d_s) {
            /* only s_n can be delta reduced */
            lean_trace(name({"type_context", "is_def_eq_detail"}), tout() << "unfold right: " << d_s->get_name() << "\n";);
            s = whnf_core(*unfold_definition(s));
        } else {
            /* both t and s can be delta reduced */
            if (is_eqp(*d_t, *d_s)) {
                /* Same constant */
                if (is_app(t) && is_app(s)) {
                    /* Heuristic: try so solve (f a =?= f b), by solving (a =?= b) */
                    scope S(*this);
                    if (is_def_eq_args(t, s) &&
                        is_def_eq(const_levels(get_app_fn(t)), const_levels(get_app_fn(s)))) {
                        S.commit();
                        return l_true;
                    }
                }
                /* Heuristic failed, then unfold both of them */
                lean_trace(name({"type_context", "is_def_eq_detail"}), tout() << "unfold left&right: " << d_t->get_name() << "\n";);
                t = whnf_core(*unfold_definition(t));
                s = whnf_core(*unfold_definition(s));
            } else {
                bool progress = false;
                if (m_transparency_mode == transparency_mode::Semireducible ||
                    m_transparency_mode == transparency_mode::All) {
                    /* Consider the following two cases

                       If t is reducible and s is not ==> reduce t
                       If s is reducible and t is not ==> reduce s

                       Remark: this can only happen if transparency_mode
                       is Semireducible or All
                    */
                    auto rd_t = is_transparent(transparency_mode::Reducible, d_t->get_name());
                    auto rd_s = is_transparent(transparency_mode::Reducible, d_s->get_name());
                    if (rd_t && !rd_s) {
                        progress = true;
                        lean_trace(name({"type_context", "is_def_eq_detail"}), tout() << "unfold (reducible) left: " << d_t->get_name() << "\n";);
                        t = whnf_core(*unfold_definition(t));
                    } else if (!rd_t && rd_s) {
                        progress = true;
                        lean_trace(name({"type_context", "is_def_eq_detail"}), tout() << "unfold (reducible) right: " << d_s->get_name() << "\n";);
                        s = whnf_core(*unfold_definition(s));
                    }
                }
                /* If we haven't reduced t nor s, then we reduce both IF the reduction is productive.
                   That is, the result of the reduction is not a recursor application. */
                if (!progress) {
                    expr new_t = reduce_if_productive(t);
                    if (!is_eqp(new_t, t) && same_head_symbol(new_t, s)) {
                        lean_trace(name({"type_context", "is_def_eq_detail"}), tout() << "unfold left (match right): " << d_t->get_name() << "\n";);
                        t = new_t;
                    } else {
                        expr new_s = reduce_if_productive(s);
                        if (!is_eqp(new_s, s) && same_head_symbol(t, new_s)) {
                            lean_trace(name({"type_context", "is_def_eq_detail"}), tout() << "unfold right (match left): " << d_s->get_name() << "\n";);
                            s = new_s;
                        } else if (is_eqp(new_t, t) && is_eqp(new_s, s)) {
                            return l_undef;
                        } else {
                            if (!is_eqp(new_t, t)) {
                                lean_trace(name({"type_context", "is_def_eq_detail"}), tout() << "unfold productive left: " << d_t->get_name() << "\n";);
                            }
                            if (!is_eqp(new_s, s)) {
                                lean_trace(name({"type_context", "is_def_eq_detail"}), tout() << "unfold productive right: " << d_s->get_name() << "\n";);
                            }
                            t = new_t;
                            s = new_s;
                        }
                    }
                }
            }
        }
        auto r = quick_is_def_eq(t, s);
        if (r != l_undef) return r;
        lean_trace(name({"type_context", "is_def_eq_detail"}), tout() << "after delta: " << t << " =?= " << s << "\n";);
    }
}

// Helper function for find_unsynth_metavar
static bool has_meta_arg(expr e) {
    if (!has_expr_metavar(e))
        return false;
    while (is_app(e)) {
        if (is_meta(app_arg(e)))
            return true;
        e = app_fn(e);
    }
    return false;
}

/** IF \c e is of the form (f ... (?m t_1 ... t_n) ...) where ?m is an unassigned
    metavariable whose type is a type class, and (?m t_1 ... t_n) must be synthesized
    by type class resolution, then we return ?m.
    Otherwise, we return none */
optional<pair<expr, expr>> type_context::find_unsynth_metavar_at_args(expr const & e) {
    if (!has_meta_arg(e))
        return optional<pair<expr, expr>>();
    buffer<expr> args;
    expr const & fn = get_app_args(e, args);
    expr type       = infer(fn);
    unsigned i      = 0;
    while (i < args.size()) {
        type = relaxed_whnf(type);
        if (!is_pi(type))
            return optional<pair<expr, expr>>();
        expr const & arg = args[i];
        if (binding_info(type).is_inst_implicit() && is_meta(arg)) {
            expr const & m = get_app_fn(arg);
            if (is_mvar(m)) {
                expr m_type = instantiate_mvars(infer(m));
                if (!has_expr_metavar_relaxed(m_type)) {
                    return some(mk_pair(m, m_type));
                }
            }
        }
        type = ::lean::instantiate(binding_body(type), arg);
        i++;
    }
    return optional<pair<expr, expr>>();
}

/** Search in \c e for an expression of the form (f ... (?m t_1 ... t_n) ...) where ?m is an unassigned
    metavariable whose type is a type class, and (?m t_1 ... t_n) must be synthesized
    by type class resolution, then we return ?m.
    Otherwise, we return none.
    This procedure goes inside lambdas. */
optional<pair<expr, expr>> type_context::find_unsynth_metavar(expr const & e) {
    if (!has_expr_metavar(e))
        return optional<pair<expr, expr>>();
    if (is_app(e)) {
        if (auto r = find_unsynth_metavar_at_args(e))
            return r;
        expr it = e;
        while (is_app(it)) {
            if (auto r = find_unsynth_metavar(app_arg(it)))
                return r;
            it = app_fn(it);
        }
        return optional<pair<expr, expr>>();
    } else if (is_lambda(e)) {
        tmp_locals locals(*this);
        expr l = locals.push_local_from_binding(e);
        return find_unsynth_metavar(::lean::instantiate(binding_body(e), l));
    } else {
        return optional<pair<expr, expr>>();
    }
}

/** \brief Create a nested type class instance of the given type, and assign it to metavariable \c m.
    Return true iff the instance was successfully created.
    \remark This method is used to resolve nested type class resolution problems. */
bool type_context::mk_nested_instance(expr const & m, expr const & m_type) {
    lean_assert(is_mvar(m));
    if (auto r = mk_class_instance(m_type)) {
        assign(m, *r);
        return true;
    } else {
        return false;
    }
}

bool type_context::on_is_def_eq_failure(expr const & e1, expr const & e2) {
    lean_trace(name({"type_context", "is_def_eq_detail"}),
               tout() << "on failure: " << e1 << " =?= " << e2 << "\n";);
    if (is_app(e1)) {
        if (auto p1 = find_unsynth_metavar(e1)) {
            lean_trace(name({"type_context", "is_def_eq_detail"}),
                       tout() << "try to synthesize: " << p1->first << " : " << p1->second << "\n";);
            if (mk_nested_instance(p1->first, p1->second)) {
                return is_def_eq_core(instantiate_mvars(e1), e2);
            }
        }
    }
    if (is_app(e2)) {
        if (auto p2 = find_unsynth_metavar(e2)) {
            lean_trace(name({"type_context", "is_def_eq_detail"}),
                       tout() << "try to synthesize: " << p2->first << " : " << p2->second << "\n";);
            if (mk_nested_instance(p2->first, p2->second)) {
                return is_def_eq_core(e1, instantiate_mvars(e2));
            }
        }
    }
    return false;
}

bool type_context::is_def_eq_core(expr const & t, expr const & s) {
    lbool r = quick_is_def_eq(t, s);
    if (r != l_undef) return r == l_true;

    flet<unsigned> inc_depth(m_is_def_eq_depth, m_is_def_eq_depth+1);
    lean_trace(name({"type_context", "is_def_eq_detail"}),
               tout() << "[" << m_is_def_eq_depth << "]: " << t << " =?= " << s << "\n";);

    expr t_n = whnf_core(t);
    expr s_n = whnf_core(s);

    if (!is_eqp(t_n, t) || !is_eqp(s_n, s)) {
        lean_trace(name({"type_context", "is_def_eq_detail"}),
                   tout() << "after whnf_core: " << t_n << " =?= " << s_n << "\n";);
        r = quick_is_def_eq(t_n, s_n);
        if (r != l_undef) return r == l_true;
    }

    check_system("is_def_eq");

    r = is_def_eq_lazy_delta(t_n, s_n);
    if (r != l_undef) return r == l_true;

    if (is_constant(t_n) && is_constant(s_n) && const_name(t_n) == const_name(s_n)) {
        scope s(*this);
        if (is_def_eq(const_levels(t_n), const_levels(s_n))) {
            s.commit();
            return true;
        }
    }

    if (is_local(t_n) && is_local(s_n) && mlocal_name(t_n) == mlocal_name(s_n))
        return true;

    if (is_app(t_n) && is_app(s_n)) {
        scope s(*this);
        if (is_def_eq_args(t_n, s_n) &&
            is_def_eq_core(get_app_fn(t_n), get_app_fn(s_n))) {
            s.commit();
            return true;
        }
    }

    if (is_def_eq_eta(t_n, s_n))
        return true;
    if (is_def_eq_eta(s_n, t_n))
        return true;
    if (is_def_eq_proof_irrel(t_n, s_n))
        return true;
    return on_is_def_eq_failure(t_n, s_n);
}

bool type_context::is_def_eq(expr const & t, expr const & s) {
    scope S(*this);
    flet<bool> in_is_def_eq(m_in_is_def_eq, true);
    bool success = is_def_eq_core(t, s);
    lean_trace(name({"type_context", "is_def_eq"}),
               tout() << t << " =?= " << s << " ... "
               << (success ? "success" : "failed") << "\n";);
    if (success) {
        S.commit();
        return true;
    } else {
        return false;
    }
}

bool type_context::relaxed_is_def_eq(expr const & e1, expr const & e2) {
    flet<transparency_mode> set(m_transparency_mode, transparency_mode::All);
    return is_def_eq(e1, e2);
}

class unification_hint_fn {
    type_context &           m_owner;
    unification_hint const & m_hint;
    buffer<optional<expr>>   m_assignment;

    bool match(expr const & pattern, expr const & e) {
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
                match(app_fn(pattern), app_fn(e)) &&
                match(app_arg(pattern), app_arg(e));
        case expr_kind::Local: case expr_kind::Meta:
            lean_unreachable();
        }
        lean_unreachable();
    }

public:
    unification_hint_fn(type_context & o, unification_hint const & hint):
        m_owner(o), m_hint(hint) {
        m_assignment.resize(m_hint.get_num_vars());
    }

    bool operator()(expr const & lhs, expr const & rhs) {
        if (!match(m_hint.get_lhs(), lhs)) {
            lean_trace(name({"type_context", "unification_hint"}), tout() << "LHS does not match\n";);
            return false;
        } else if (!match(m_hint.get_rhs(), rhs)) {
            lean_trace(name({"type_context", "unification_hint"}), tout() << "RHS does not match\n";);
            return false;
        } else {
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
                bool success = m_owner.is_def_eq(new_lhs, new_rhs);
                lean_trace(name({"type_context", "unification_hint"}),
                           tout() << new_lhs << " =?= " << new_rhs << "..."
                           << (success ? "success" : "failed") << "\n";);
                if (!success) return false;
            }
            lean_trace(name({"type_context", "unification_hint"}),
                       tout() << "hint successfully applied\n";);
            return true;
        }
    }
};

bool type_context::try_unification_hint(unification_hint const & hint, expr const & e1, expr const & e2) {
    scope s(*this);
    if (unification_hint_fn(*this, hint)(e1, e2)) {
        s.commit();
        return true;
    } else {
        return false;
    }
}

bool type_context::try_unification_hints(expr const & e1, expr const & e2) {
    expr e1_fn = get_app_fn(e1);
    expr e2_fn = get_app_fn(e2);
    if (is_constant(e1_fn) && is_constant(e2_fn)) {
        buffer<unification_hint> hints;
        get_unification_hints(env(), const_name(e1_fn), const_name(e2_fn), hints);
        for (unification_hint const & hint : hints) {
            lean_trace(name({"type_context", "unification_hint"}),
                       tout() << e1 << " =?= " << e2
                       << ", pattern: " << hint.get_lhs() << " =?= " << hint.get_rhs() << "\n";);
            if (try_unification_hint(hint, e1, e2) ||
                try_unification_hint(hint, e2, e1)) {
                return true;
            }
        }
    }
    return false;
}

/* -------------
   Type classes
   ------------- */

/** \brief If the constant \c e is a class, return its name */
optional<name> type_context::constant_is_class(expr const & e) {
    name const & cls_name = const_name(e);
    if (lean::is_class(env(), cls_name)) {
        return optional<name>(cls_name);
    } else {
        return optional<name>();
    }
}

optional<name> type_context::is_full_class(expr type) {
    type = whnf(type);
    if (is_pi(type)) {
        tmp_locals locals(*this);
        return is_full_class(::lean::instantiate(binding_body(type), locals.push_local_from_binding(type)));
    } else {
        expr f = get_app_fn(type);
        if (!is_constant(f))
            return optional<name>();
        return constant_is_class(f);
    }
}

/** \brief Partial/Quick test for is_class. Result
    l_true:   \c type is a class, and the name of the class is stored in \c result.
    l_false:  \c type is not a class.
    l_undef:  procedure did not establish whether \c type is a class or not. */
lbool type_context::is_quick_class(expr const & type, name & result) {
    expr const * it = &type;
    while (true) {
        switch (it->kind()) {
        case expr_kind::Var:  case expr_kind::Sort:   case expr_kind::Local:
        case expr_kind::Meta: case expr_kind::Lambda: case expr_kind::Let:
            return l_false;
        case expr_kind::Macro:
            return l_undef;
        case expr_kind::Constant:
            if (auto r = constant_is_class(*it)) {
                result = *r;
                return l_true;
            } else if (!is_transparent(const_name(*it))) {
                return l_false;
            } else {
                return l_undef;
            }
        case expr_kind::App: {
            expr const & f = get_app_fn(*it);
            if (is_constant(f)) {
                if (auto r = constant_is_class(f)) {
                    result = *r;
                    return l_true;
                } else if (!is_transparent(const_name(f))) {
                    return l_false;
                } else {
                    return l_undef;
                }
            } else if (is_lambda(f) || is_macro(f)) {
                return l_undef;
            } else {
                return l_false;
            }
        }
        case expr_kind::Pi:
            it = &binding_body(*it);
            break;
        }
    }
}

/** \brief Return true iff \c type is a class or Pi that produces a class. */
optional<name> type_context::is_class(expr const & type) {
    name result;
    switch (is_quick_class(type, result)) {
    case l_true:  return optional<name>(result);
    case l_false: return optional<name>();
    case l_undef: break;
    }
    return is_full_class(type);
}

bool type_context::compatible_local_instances(bool frozen_only) {
    unsigned i  = 0;
    bool failed = false;
    m_cache.m_init_local_context.for_each([&](local_decl const & decl) {
            if (failed) return;
            if (frozen_only && !m_cache.m_init_local_context.is_frozen(decl.get_name()))
                return;
            if (auto cname = is_class(decl.get_type())) {
                if (i == m_cache.m_local_instances.size()) {
                    /* initial local context has more local instances than the ones cached at found m_local_instances */
                    failed = true;
                    return;
                }
                if (decl.get_name() != mlocal_name(m_cache.m_local_instances[i].second)) {
                    /* local instance in initial local constext is not compatible with the one cached at m_local_instances */
                    failed = true;
                    return;
                }
                i++;
            }
        });
    return i == m_cache.m_local_instances.size();
}

void type_context::set_local_instances() {
    m_cache.m_instance_cache.clear();
    m_cache.m_subsingleton_cache.clear();
    m_cache.m_local_instances.clear();
    m_cache.m_init_local_context.for_each([&](local_decl const & decl) {
            if (auto cls_name = is_class(decl.get_type())) {
                m_cache.m_local_instances.emplace_back(*cls_name, decl.mk_ref());
            }
        });
}

void type_context::init_local_instances() {
    if (m_cache.m_frozen_mode) {
        lean_assert(m_cache.m_local_instances_initialized);
        /* Check if the local instances are really compatible.
           See comment at type_context_cache. */
        lean_cond_assert("type_context", compatible_local_instances(true));
    } else if (!m_cache.m_local_instances_initialized) {
        /* default type class resolution mode */
        bool frozen_only = false;
        if (!compatible_local_instances(frozen_only)) {
            set_local_instances();
        }
        m_cache.m_local_instances_initialized = true;
    }
    lean_assert(m_cache.m_local_instances_initialized);
}

[[ noreturn ]] static void throw_class_exception(char const * msg, expr const & m) { throw_generic_exception(msg, m); }

struct instance_synthesizer {
    struct stack_entry {
        /* We only use transitive instances when we can solve the problem in a single step.
           That is, the transitive instance does not have any instance argument, OR
           it uses local instances to fill them.
           We accomplish that by not considering global instances when solving
           transitive instance subproblems. */
        expr     m_mvar;
        unsigned m_depth;
        bool     m_trans_inst_subproblem;
        stack_entry(expr const & m, unsigned d, bool s = false):
            m_mvar(m), m_depth(d), m_trans_inst_subproblem(s) {}
    };

    struct state {
        bool               m_trans_inst_subproblem;
        list<stack_entry>  m_stack; // stack of meta-variables that need to be synthesized;
    };

    struct choice {
        list<expr>         m_local_instances;
        list<name>         m_trans_instances;
        list<name>         m_instances;
        state              m_state;
    };

    type_context &        m_ctx;
    expr                  m_main_mvar;
    state                 m_state;    // active state
    buffer<choice>        m_choices;
    bool                  m_displayed_trace_header;
    transparency_mode     m_old_transparency_mode;

    instance_synthesizer(type_context & ctx):
        m_ctx(ctx),
        m_displayed_trace_header(false),
        m_old_transparency_mode(m_ctx.m_transparency_mode) {
        lean_assert(m_ctx.in_tmp_mode());
        m_ctx.m_transparency_mode = transparency_mode::Reducible;
    }

    ~instance_synthesizer() {
        for (unsigned i = 0; i < m_choices.size(); i++) {
            m_ctx.pop_scope();
        }
        m_ctx.m_transparency_mode = m_old_transparency_mode;
    }

    environment const & env() const { return m_ctx.env(); }

    bool is_done() const {
        return empty(m_state.m_stack);
    }

    void trace(unsigned depth, expr const & mvar, expr const & mvar_type, expr const & r) {
        auto out = tout();
        if (!m_displayed_trace_header && m_choices.size() == 1) {
            out << tclass("class_instances");
            if (m_ctx.m_cache.m_pip) {
                if (auto fname = m_ctx.m_cache.m_pip->get_file_name()) {
                    out << fname << ":";
                }
                if (m_ctx.m_cache.m_ci_pos)
                    out << m_ctx.m_cache.m_ci_pos->first << ":" << m_ctx.m_cache.m_ci_pos->second << ":";
            }
            out << " class-instance resolution trace" << endl;
            m_displayed_trace_header = true;
        }
        out << tclass("class_instances") << "(" << depth << ") ";
        out << mvar << " : " << m_ctx.instantiate_mvars(mvar_type) << " := " << r << endl;
    }

    /* Try to synthesize e.m_mvar using instance inst : inst_type.
       trans_inst is true if inst is a transitive instance. */
    bool try_instance(stack_entry const & e, expr const & inst, expr const & inst_type, bool trans_inst) {
        try {
            type_context::tmp_locals locals(m_ctx);
            expr const & mvar = e.m_mvar;
            expr mvar_type    = m_ctx.infer(mvar);
            while (true) {
                mvar_type = m_ctx.relaxed_whnf(mvar_type);
                if (!is_pi(mvar_type))
                    break;
                expr local  = locals.push_local_from_binding(mvar_type);
                mvar_type   = instantiate(binding_body(mvar_type), local);
            }
            expr type  = inst_type;
            expr r     = inst;
            buffer<expr> new_inst_mvars;
            while (true) {
                type = m_ctx.relaxed_whnf(type);
                if (!is_pi(type))
                    break;
                expr new_mvar = m_ctx.mk_tmp_mvar(locals.mk_pi(binding_domain(type)));
                if (binding_info(type).is_inst_implicit()) {
                    new_inst_mvars.push_back(new_mvar);
                }
                expr new_arg = mk_app(new_mvar, locals.as_buffer());
                r    = mk_app(r, new_arg);
                type = instantiate(binding_body(type), new_arg);
            }
            lean_trace_plain("class_instances", trace(e.m_depth, mk_app(mvar, locals.as_buffer()), mvar_type, r););
            if (!m_ctx.is_def_eq(mvar_type, type)) {
                return false;
            }
            r = locals.mk_lambda(r);
            m_ctx.assign(mvar, r);
            // copy new_inst_mvars to stack
            unsigned i = new_inst_mvars.size();
            while (i > 0) {
                --i;
                m_state.m_stack = cons(stack_entry(new_inst_mvars[i], e.m_depth+1, trans_inst), m_state.m_stack);
            }
            return true;
        } catch (exception &) {
            return false;
        }
    }

    bool try_instance(stack_entry const & e, name const & inst_name, bool trans_inst) {
        if (auto decl = env().find(inst_name)) {
            buffer<level> ls_buffer;
            unsigned num_univ_ps = decl->get_num_univ_params();
            for (unsigned i = 0; i < num_univ_ps; i++)
                ls_buffer.push_back(m_ctx.mk_tmp_univ_mvar());
            levels ls = to_list(ls_buffer.begin(), ls_buffer.end());
            expr inst_cnst = mk_constant(inst_name, ls);
            expr inst_type = instantiate_type_univ_params(*decl, ls);
            return try_instance(e, inst_cnst, inst_type, trans_inst);
        } else {
            return false;
        }
    }

    list<expr> get_local_instances(name const & cname) {
        buffer<expr> selected;
        for (pair<name, expr> const & p : m_ctx.m_cache.m_local_instances) {
            if (p.first == cname)
                selected.push_back(p.second);
        }
        return to_list(selected);
    }

    bool mk_choice_point(expr const & mvar) {
        lean_assert(is_metavar(mvar));
        if (m_choices.size() > m_ctx.m_cache.m_ci_max_depth) {
            throw_class_exception("maximum class-instance resolution depth has been reached "
                                  "(the limit can be increased by setting option 'class.instance_max_depth') "
                                  "(the class-instance resolution trace can be visualized "
                                  "by setting option 'trace.class_instances')",
                                  m_ctx.infer(m_main_mvar));
        }
        // Remark: we initially tried to reject branches where mvar_type contained unassigned metavariables.
        // The idea was to make the procedure easier to understand.
        // However, it turns out this is too restrictive. The group_theory folder contains the following instance.
        //     nsubg_setoid : Π {A : Type} [s : group A] (N : set A) [is_nsubg : @is_normal_subgroup A s N], setoid A
        // When it is used, it creates a subproblem for
        //    is_nsubg : @is_normal_subgroup A s ?N
        // where ?N is not known. Actually, we can only find the value for ?N by constructing the instance is_nsubg.
        expr mvar_type       = m_ctx.instantiate_mvars(mlocal_type(mvar));
        bool toplevel_choice = m_choices.empty();
        m_choices.push_back(choice());
        m_ctx.push_scope();
        choice & r = m_choices.back();
        auto cname = m_ctx.is_class(mvar_type);
        if (!cname)
            return false;
        r.m_local_instances = get_local_instances(*cname);
        if (m_ctx.m_cache.m_ci_trans_instances && toplevel_choice) {
            // we only use transitive instances in the top-level
            r.m_trans_instances = get_class_derived_trans_instances(env(), *cname);
        }
        r.m_instances = get_class_instances(env(), *cname);
        if (empty(r.m_local_instances) && empty(r.m_trans_instances) && empty(r.m_instances))
            return false;
        r.m_state = m_state;
        return true;
    }

    bool process_next_alt_core(stack_entry const & e, list<expr> & insts) {
        while (!empty(insts)) {
            expr inst       = head(insts);
            insts           = tail(insts);
            expr inst_type  = m_ctx.infer(inst);
            bool trans_inst = false;
            if (try_instance(e, inst, inst_type, trans_inst))
                return true;
        }
        return false;
    }

    bool process_next_alt_core(stack_entry const & e, list<name> & inst_names, bool trans_inst) {
        while (!empty(inst_names)) {
            name inst_name    = head(inst_names);
            inst_names        = tail(inst_names);
            if (try_instance(e, inst_name, trans_inst))
                return true;
        }
        return false;
    }

    bool process_next_alt(stack_entry const & e) {
        lean_assert(m_choices.size() > 0);
        lean_assert(!m_choices.empty());
        buffer<choice> & cs = m_choices;
        list<expr> locals = cs.back().m_local_instances;
        if (process_next_alt_core(e, locals)) {
            cs.back().m_local_instances = locals;
            return true;
        }
        cs.back().m_local_instances = list<expr>();
        if (!e.m_trans_inst_subproblem) {
            list<name> trans_insts = cs.back().m_trans_instances;
            if (process_next_alt_core(e, trans_insts, true)) {
                cs.back().m_trans_instances = trans_insts;
                return true;
            }
            cs.back().m_trans_instances = list<name>();
            list<name> insts = cs.back().m_instances;
            if (process_next_alt_core(e, insts, false)) {
                cs.back().m_instances = insts;
                return true;
            }
            cs.back().m_instances = list<name>();
        }
        return false;
    }

    bool process_next_mvar() {
        lean_assert(!is_done());
        stack_entry e = head(m_state.m_stack);
        if (!mk_choice_point(e.m_mvar))
            return false;
        m_state.m_stack = tail(m_state.m_stack);
        return process_next_alt(e);
    }

    bool backtrack() {
        if (m_choices.empty())
            return false;
        lean_assert(!m_choices.empty());
        while (true) {
            m_choices.pop_back();
            m_ctx.pop_scope();
            if (m_choices.empty())
                return false;
            m_state         = m_choices.back().m_state;
            stack_entry e   = head(m_state.m_stack);
            m_state.m_stack = tail(m_state.m_stack);
            if (process_next_alt(e))
                return true;
        }
    }

    optional<expr> search() {
        while (!is_done()) {
            if (!process_next_mvar()) {
                if (!backtrack())
                    return none_expr();
            }
        }
        return some_expr(m_ctx.instantiate_mvars(m_main_mvar));
    }

    optional<expr> next_solution() {
        if (m_choices.empty())
            return none_expr();
        m_ctx.pop_scope(); m_ctx.push_scope(); // restore assignment
        m_state         = m_choices.back().m_state;
        stack_entry e   = head(m_state.m_stack);
        m_state.m_stack = tail(m_state.m_stack);
        if (process_next_alt(e))
            return search();
        else if (backtrack())
            return search();
        else
            return none_expr();
    }

    void cache_result(expr const & type, optional<expr> const & inst) {
        m_ctx.m_cache.m_instance_cache.insert(mk_pair(type, inst));
    }

    optional<expr> ensure_no_meta(optional<expr> r) {
        while (true) {
            if (!r) {
                cache_result(m_ctx.infer(m_main_mvar), r);
                return none_expr();
            }
            if (!has_expr_metavar_relaxed(*r)) {
                cache_result(m_ctx.infer(m_main_mvar), r);
                return r;
            }
            r = next_solution();
        }
    }

    optional<expr> mk_class_instance_core(expr const & type) {
        /* We do not cache results when multiple instances have to be generated. */
        auto it = m_ctx.m_cache.m_instance_cache.find(type);
        if (it != m_ctx.m_cache.m_instance_cache.end()) {
            /* instance/failure is already cached */
            lean_trace("class_instances",
                       if (it->second)
                           tout() << "cached instance for " << type << "\n" << *(it->second) << "\n";
                       else
                           tout() << "cached failure for " << type << "\n";);
            return it->second;
        }
        m_state          = state();
        m_main_mvar      = m_ctx.mk_tmp_mvar(type);
        m_state.m_stack  = to_list(stack_entry(m_main_mvar, 0));
        auto r = search();
        return ensure_no_meta(r);
    }

    optional<expr> operator()(expr const & type) {
        lean_trace_init_bool("class_instances", get_pp_purify_metavars_name(), false);
        lean_trace_init_bool("class_instances", get_pp_implicit_name(), true);
        auto r = mk_class_instance_core(type);
        if (r) {
            for (unsigned i = 0; i < m_choices.size(); i++) {
                m_ctx.commit_scope();
            }
            m_choices.clear();
        }
        return r;
    }
};

optional<expr> type_context::mk_class_instance(expr const & type) {
    if (in_tmp_mode()) {
        return instance_synthesizer(*this)(type);
    } else {
        tmp_mode_scope s(*this);
        return instance_synthesizer(*this)(type);
    }
}

optional<expr> type_context::mk_subsingleton_instance(expr const & type) {
    auto it = m_cache.m_subsingleton_cache.find(type);
    if (it != m_cache.m_subsingleton_cache.end())
        return it->second;
    expr Type  = whnf(infer(type));
    if (!is_sort(Type)) {
        m_cache.m_subsingleton_cache.insert(mk_pair(type, none_expr()));
        return none_expr();
    }
    level lvl    = sort_level(Type);
    expr subsingleton;
    if (is_standard(env()))
        subsingleton = mk_app(mk_constant(get_subsingleton_name(), {lvl}), type);
    else
        subsingleton = whnf(mk_app(mk_constant(get_is_trunc_is_prop_name(), {lvl}), type));
    auto r = mk_class_instance(subsingleton);
    m_cache.m_subsingleton_cache.insert(mk_pair(type, r));
    return r;
}

tmp_type_context::tmp_type_context(type_context & tctx, unsigned num_umeta, unsigned num_emeta): m_tctx(tctx) {
    m_tmp_uassignment.resize(num_umeta, none_level());
    m_tmp_eassignment.resize(num_emeta, none_expr());
}

bool tmp_type_context::is_def_eq(expr const & e1, expr const & e2) {
    type_context::tmp_mode_scope_with_buffers tmp_scope(m_tctx, m_tmp_uassignment, m_tmp_eassignment);
    return m_tctx.is_def_eq(e1, e2);
}

expr tmp_type_context::infer(expr const & e) {
    type_context::tmp_mode_scope_with_buffers tmp_scope(m_tctx, m_tmp_uassignment, m_tmp_eassignment);
    return m_tctx.infer(e);
}

expr tmp_type_context::whnf(expr const & e) {
    // TODO(dhs): do I need to set the buffers for whnf?
    type_context::tmp_mode_scope_with_buffers tmp_scope(m_tctx, m_tmp_uassignment, m_tmp_eassignment);
    return m_tctx.whnf(e);
}

level tmp_type_context::mk_tmp_univ_mvar() {
    type_context::tmp_mode_scope_with_buffers tmp_scope(m_tctx, m_tmp_uassignment, m_tmp_eassignment);
    return m_tctx.mk_tmp_univ_mvar();
}

expr tmp_type_context::mk_tmp_mvar(expr const & type) {
    type_context::tmp_mode_scope_with_buffers tmp_scope(m_tctx, m_tmp_uassignment, m_tmp_eassignment);
    return m_tctx.mk_tmp_mvar(type);
}

bool tmp_type_context::is_uassigned(unsigned i) {
    lean_assert(i < m_tmp_uassignment.size());
    return static_cast<bool>(m_tmp_uassignment[i]);
}

bool tmp_type_context::is_eassigned(unsigned i) {
    lean_assert(i < m_tmp_eassignment.size());
    return static_cast<bool>(m_tmp_eassignment[i]);
}

void tmp_type_context::clear_eassignment() {
    m_tmp_eassignment.clear();
}

expr tmp_type_context::instantiate_mvars(expr const & e) {
    type_context::tmp_mode_scope_with_buffers tmp_scope(m_tctx, m_tmp_uassignment, m_tmp_eassignment);
    return m_tctx.instantiate_mvars(e);
}

void initialize_type_context() {
    register_trace_class("class_instances");
    register_trace_class(name({"type_context", "unification_hint"}));
    register_trace_class(name({"type_context", "is_def_eq"}));
    register_trace_class(name({"type_context", "is_def_eq_detail"}));
    g_class_instance_max_depth     = new name{"class", "instance_max_depth"};
    g_class_trans_instances        = new name{"class", "trans_instances"};
    register_unsigned_option(*g_class_instance_max_depth, LEAN_DEFAULT_CLASS_INSTANCE_MAX_DEPTH,
                             "(class) max allowed depth in class-instance resolution");
    register_bool_option(*g_class_trans_instances,  LEAN_DEFAULT_CLASS_TRANS_INSTANCES,
                         "(class) use automatically derived instances from the transitive closure of "
                         "the structure instance graph");
}

void finalize_type_context() {
    delete g_class_instance_max_depth;
    delete g_class_trans_instances;
}
}
