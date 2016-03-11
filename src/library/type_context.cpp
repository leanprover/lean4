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
#include "library/metavar_util.h"
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

/* =====================
   type_context_cache
   ===================== */

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

/* =====================
   type_context::tmp_locals
   ===================== */
type_context::tmp_locals::~tmp_locals() {
    for (unsigned i = 0; i < m_locals.size(); i++)
        m_ctx.pop_local();
}

/* =====================
   type_context
   ===================== */

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

bool type_context::should_unfold_macro(expr const & e) {
    /* If m_transparency_mode is set to ALL, then we unfold all
       macros. In this way, we make sure type inference does not fail. */
    return m_transparency_mode == transparency_mode::All || m_cache->should_unfold_macro(e);
}

optional<expr> type_context::expand_macro(expr const & e) {
    lean_assert(is_macro(e));
    if (should_unfold_macro(e)) {
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
    flet<transparency_mode> set(m_transparency_mode, transparency_mode::All);
    return infer_core(e);
}

expr type_context::infer_core(expr const & e) {
    lean_assert(!is_var(e));
    lean_assert(closed(e));

    auto & cache = m_cache->m_infer_cache;
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
    } else if (m_tmp_mode && is_idx_metavar(e)) {
        /* tmp metavariables should only occur in tmp_mode */
        return mlocal_type(e);
    } else {
        lean_unreachable();
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
    type_context_as_extension_context ext(*this);
    return def.check_type(e, ext, infer_only).first;
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
        r = mk_pi(binding_name(es[i]), ds[i], r, binding_info(es[i]));
    }
    return r;
}

optional<level> type_context::get_level_core(expr const & A) {
    expr A_type = whnf(infer_core(A));
    while (true) {
        if (is_sort(A_type)) {
            return some_level(sort_level(A_type));
        } else if (is_mvar(A_type)) {
            if (auto v = get_assignment(A_type)) {
                A_type = *v;
            } else if (!m_tmp_mode && is_metavar_decl_ref(A_type)) {
                /* We should only assign A_type IF we are not in tmp mode. */
                level r = m_mctx.mk_univ_metavar_decl();
                assign(A_type, mk_sort(r));
                return some_level(r);
            } else if (m_tmp_mode && is_idx_metavar(A_type)) {
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

level type_context::mk_tmp_univ_mvar() {
    unsigned idx = m_tmp_uassignment.size();
    m_tmp_uassignment.push_back(none_level());
    return mk_idx_metauniv(idx);
}

/* -----------------------------------
   Uniform interface to tmp/regular metavariables
   ----------------------------------- */

bool type_context::is_mvar(level const & l) const {
    if (m_tmp_mode)
        return is_idx_metauniv(l);
    else
        return is_metavar_decl_ref(l);
}

bool type_context::is_mvar(expr const & e) const {
    if (m_tmp_mode)
        return is_idx_metavar(e);
    else
        return is_metavar_decl_ref(e);
}

bool type_context::is_assigned(level const & l) const {
    const_cast<type_context*>(this)->m_used_assignment = true;
    if (m_tmp_mode)
        return static_cast<bool>(get_tmp_assignment(l));
    else
        return m_mctx.is_assigned(l);
}

bool type_context::is_assigned(expr const & e) const {
    const_cast<type_context*>(this)->m_used_assignment = true;
    if (m_tmp_mode)
        return static_cast<bool>(get_tmp_assignment(e));
    else
        return m_mctx.is_assigned(e);
}

optional<level> type_context::get_assignment(level const & l) const {
    const_cast<type_context*>(this)->m_used_assignment = true;
    if (m_tmp_mode)
        return get_tmp_assignment(l);
    else
        return m_mctx.get_assignment(l);
}

optional<expr> type_context::get_assignment(expr const & e) const {
    const_cast<type_context*>(this)->m_used_assignment = true;
    if (m_tmp_mode)
        return get_tmp_assignment(e);
    else
        return m_mctx.get_assignment(e);
}

void type_context::assign(level const & u, level const & l) {
    m_used_assignment = true;
    if (m_tmp_mode)
        assign_tmp(u, l);
    else
        m_mctx.assign(u, l);
}

void type_context::assign(expr const & m, expr const & v) {
    m_used_assignment = true;
    if (m_tmp_mode)
        assign_tmp(m, v);
    else
        m_mctx.assign(m, v);
}

level type_context::instantiate(level const & l) {
    return ::lean::instantiate(*this, l);
}

expr type_context::instantiate(expr const & e) {
    return ::lean::instantiate(*this, e);
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


bool type_context::is_def_eq_core(expr const & t, expr const & s) {
    check_system("is_definitionally_equal");
    // TODO(Leo)
    return false;
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
