/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/interrupt.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/for_each_fn.h"
#include "library/projection.h"
#include "library/normalize.h"
#include "library/replace_visitor.h"
#include "library/type_inference.h"

namespace lean {
static name * g_prefix = nullptr;

struct type_inference::ext_ctx : public extension_context {
    type_inference & m_owner;

    ext_ctx(type_inference & o):m_owner(o) {}

    virtual environment const & env() const { return m_owner.m_env; }

    virtual pair<expr, constraint_seq> whnf(expr const & e) {
        return mk_pair(m_owner.whnf(e), constraint_seq());
    }

    virtual pair<bool, constraint_seq> is_def_eq(expr const & e1, expr const & e2, delayed_justification &) {
        return mk_pair(m_owner.is_def_eq(e1, e2), constraint_seq());
    }

    virtual pair<expr, constraint_seq> check_type(expr const & e, bool) {
        return mk_pair(m_owner.infer(e), constraint_seq());
    }

    virtual name mk_fresh_name() {
        return m_owner.m_ngen.next();
    }

    virtual optional<expr> is_stuck(expr const &) {
        return none_expr();
    }
};

type_inference::type_inference(environment const & env):
    m_env(env),
    m_ngen(*g_prefix),
    m_ext_ctx(new ext_ctx(*this)),
    m_proj_info(get_projection_info_map(env)) {
}

type_inference::~type_inference() {
}

bool type_inference::is_opaque(declaration const & d) const {
    if (d.is_theorem())
        return true;
    name const & n = d.get_name();
    return m_proj_info.contains(n) || is_extra_opaque(n);
}

optional<expr> type_inference::expand_macro(expr const & m) {
    lean_assert(is_macro(m));
    return macro_def(m).expand(m, *m_ext_ctx);
}

optional<expr> type_inference::reduce_projection(expr const & e) {
    expr const & f = get_app_fn(e);
    if (!is_constant(f))
        return none_expr();
    projection_info const * info = m_proj_info.find(const_name(f));
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

optional<expr> type_inference::norm_ext(expr const & e) {
    if (auto r = reduce_projection(e)) {
        return r;
    } else if (auto r = m_env.norm_ext()(e, *m_ext_ctx)) {
        return some_expr(r->first);
    } else {
        return none_expr();
    }
}

expr type_inference::whnf_core(expr const & e) {
    check_system("whnf");
    switch (e.kind()) {
    case expr_kind::Var: case expr_kind::Sort: case expr_kind::Meta: case expr_kind::Local:
    case expr_kind::Pi:  case expr_kind::Constant: case expr_kind::Lambda:
        return e;
    case expr_kind::Macro:
        if (auto m = expand_macro(e))
            return whnf_core(*m);
        else
            return e;
        break;
    case expr_kind::App: {
        buffer<expr> args;
        expr f0 = get_app_rev_args(e, args);
        expr f = whnf_core(f0);
        if (is_lambda(f)) {
            unsigned m = 1;
            unsigned num_args = args.size();
            while (is_lambda(binding_body(f)) && m < num_args) {
                f = binding_body(f);
                m++;
            }
            lean_assert(m <= num_args);
            return whnf_core(mk_rev_app(instantiate(binding_body(f), m, args.data() + (num_args - m)),
                                        num_args - m, args.data()));
        } else {
            return f == f0 ? e : whnf_core(mk_rev_app(f, args.size(), args.data()));
        }
    }}
    lean_unreachable();
}

/** \brief Expand \c e if it is non-opaque constant with height >= h */
expr type_inference::unfold_name_core(expr e, unsigned h) {
    if (is_constant(e)) {
        if (auto d = m_env.find(const_name(e))) {
            if (d->is_definition() && !is_opaque(*d) && d->get_height() >= h &&
                length(const_levels(e)) == d->get_num_univ_params())
                return unfold_name_core(instantiate_value_univ_params(*d, const_levels(e)), h);
        }
    }
    return e;
}

/** \brief Expand constants and application where the function is a constant.
    The unfolding is only performend if the constant corresponds to
    a non-opaque definition with height >= h */
expr type_inference::unfold_names(expr const & e, unsigned h) {
    if (is_app(e)) {
        expr f0 = get_app_fn(e);
        expr f  = unfold_name_core(f0, h);
        if (is_eqp(f, f0)) {
            return e;
        } else {
            buffer<expr> args;
            get_app_rev_args(e, args);
            return mk_rev_app(f, args);
        }
    } else {
        return unfold_name_core(e, h);
    }
}

/** \brief Return some definition \c d iff \c e is a target for delta-reduction,
    and the given definition is the one to be expanded. */
optional<declaration> type_inference::is_delta(expr const & e) const {
    expr const & f = get_app_fn(e);
    if (is_constant(f)) {
        if (auto d = m_env.find(const_name(f)))
            if (d->is_definition() && !is_opaque(*d))
                return d;
    }
    return none_declaration();
}

/** \brief Weak head normal form core procedure that performs delta reduction
    for non-opaque constants with definitional height greater than or equal to \c h.

    This method is based on <tt>whnf_core(expr const &)</tt> and \c unfold_names.
    \remark This method does not use normalization extensions attached in the environment.
*/
expr type_inference::whnf_core(expr e, unsigned h) {
    while (true) {
        expr new_e = unfold_names(whnf_core(e), h);
        if (is_eqp(e, new_e))
            return e;
        e = new_e;
    }
}

/** \brief Put expression \c t in weak head normal form */
expr type_inference::whnf(expr const & e) {
    // Do not cache easy cases
    switch (e.kind()) {
    case expr_kind::Var: case expr_kind::Sort: case expr_kind::Meta: case expr_kind::Local: case expr_kind::Pi:
        return e;
    case expr_kind::Lambda: case expr_kind::Macro: case expr_kind::App: case expr_kind::Constant:
        break;
    }

    expr t = e;
    while (true) {
        expr t1 = whnf_core(t, 0);
        if (auto new_t = norm_ext(t1)) {
            t  = *new_t;
        } else {
            return t1;
        }
    }
}

bool type_inference::is_def_eq(level const & l1, level const & l2) {
    if (is_equivalent(l1, l2)) {
        return true;
    }

    if (is_uvar(l1)) {
        if (auto v = get_assignment(l1)) {
            return is_def_eq(*v, l2);
        } else {
            update_assignment(l1, l2);
            return true;
        }
    }

    if (is_uvar(l2)) {
        if (auto v = get_assignment(l2)) {
            return is_def_eq(l1, *v);
        } else {
            update_assignment(l2, l1);
            return true;
        }
    }

    level new_l1 = normalize(instantiate_uvars(l1));
    level new_l2 = normalize(instantiate_uvars(l2));

    if (ignore_universe_def_eq(new_l1, new_l2))
        return true;

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

bool type_inference::is_def_eq(levels const & ls1, levels const & ls2) {
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

/** \brief Given \c e of the form <tt>?m t_1 ... t_n</tt>, where
    ?m is an assigned mvar, substitute \c ?m with its assignment. */
expr type_inference::subst_mvar(expr const & e) {
    buffer<expr> args;
    expr const & m   = get_app_rev_args(e, args);
    lean_assert(is_mvar(m));
    expr const * v = get_assignment(m);
    lean_assert(v);
    return apply_beta(*v, args.size(), args.data());
}

bool type_inference::has_assigned_uvar(level const & l) const {
    if (!has_meta(l))
        return false;
    bool found = false;
    for_each(l, [&](level const & l) {
            if (!has_meta(l))
                return false; // stop search
            if (found)
                return false;  // stop search
            if (is_uvar(l) && is_assigned(l)) {
                found = true;
                return false; // stop search
            }
            return true; // continue search
        });
    return found;
}

bool type_inference::has_assigned_uvar(levels const & ls) const {
    for (level const & l : ls) {
        if (has_assigned_uvar(l))
            return true;
    }
    return false;
}

bool type_inference::has_assigned_uvar_mvar(expr const & e) const {
    if (!has_expr_metavar(e) && !has_univ_metavar(e))
        return false;
    bool found = false;
    for_each(e, [&](expr const & e, unsigned) {
            if (!has_expr_metavar(e) && !has_univ_metavar(e))
                return false; // stop search
            if (found)
                return false; // stop search
            if ((is_mvar(e) && is_assigned(e)) ||
                (is_constant(e) && has_assigned_uvar(const_levels(e))) ||
                (is_sort(e) && has_assigned_uvar(sort_level(e)))) {
                found = true;
                return false; // stop search
            }
            return true; // continue search
        });
    return found;
}

level type_inference::instantiate_uvars(level const & l) {
    if (!has_assigned_uvar(l))
        return l;
    return replace(l, [&](level const & l) {
            if (!has_meta(l)) {
                return some_level(l);
            } else if (is_uvar(l)) {
                if (auto v1 = get_assignment(l)) {
                    level v2 = instantiate_uvars(*v1);
                    if (*v1 != v2) {
                        update_assignment(l, v2);
                        return some_level(v2);
                    } else {
                        return some_level(*v1);
                    }
                }
            }
            return none_level();
        });
}

struct instantiate_uvars_mvars_fn : public replace_visitor {
    type_inference & m_owner;

    level visit_level(level const & l) {
        return m_owner.instantiate_uvars(l);
    }

    levels visit_levels(levels const & ls) {
        return map_reuse(ls,
                         [&](level const & l) { return visit_level(l); },
                         [](level const & l1, level const & l2) { return is_eqp(l1, l2); });
    }

    virtual expr visit_sort(expr const & s) {
        return update_sort(s, visit_level(sort_level(s)));
    }

    virtual expr visit_constant(expr const & c) {
        return update_constant(c, visit_levels(const_levels(c)));
    }

    virtual expr visit_local(expr const & e) {
        return update_mlocal(e, visit(mlocal_type(e)));
    }

    virtual expr visit_meta(expr const & m) {
        if (m_owner.is_mvar(m)) {
            if (auto v1 = m_owner.get_assignment(m)) {
                if (!has_expr_metavar(*v1)) {
                    return *v1;
                } else {
                    expr v2 = m_owner.instantiate_uvars_mvars(*v1);
                    if (v2 != *v1)
                        m_owner.update_assignment(m, v2);
                    return v2;
                }
            } else {
                return m;
            }
        } else {
            return m;
        }
    }

    virtual expr visit_app(expr const & e) {
        buffer<expr> args;
        expr const & f = get_app_rev_args(e, args);
        if (m_owner.is_mvar(f)) {
            if (auto v = m_owner.get_assignment(f)) {
                expr new_app = apply_beta(*v, args.size(), args.data());
                if (has_expr_metavar(new_app))
                    return visit(new_app);
                else
                    return new_app;
            }
        }
        expr new_f = visit(f);
        buffer<expr> new_args;
        bool modified = !is_eqp(new_f, f);
        for (expr const & arg : args) {
            expr new_arg = visit(arg);
            if (!is_eqp(arg, new_arg))
                modified = true;
            new_args.push_back(new_arg);
        }
        if (!modified)
            return e;
        else
            return mk_rev_app(new_f, new_args, e.get_tag());
    }

    virtual expr visit_macro(expr const & e) {
        lean_assert(is_macro(e));
        buffer<expr> new_args;
        for (unsigned i = 0; i < macro_num_args(e); i++)
            new_args.push_back(visit(macro_arg(e, i)));
        return update_macro(e, new_args.size(), new_args.data());
    }

    virtual expr visit(expr const & e) {
        if (!has_expr_metavar(e) && !has_univ_metavar(e))
            return e;
        else
            return replace_visitor::visit(e);
    }

public:
    instantiate_uvars_mvars_fn(type_inference & o):m_owner(o) {}

    expr operator()(expr const & e) { return visit(e); }
};

expr type_inference::instantiate_uvars_mvars(expr const & e) {
    if (!has_assigned_uvar_mvar(e))
        return e;
    else
        return instantiate_uvars_mvars_fn(*this)(e);
}

bool type_inference::is_prop(expr const & e) {
    if (m_env.impredicative()) {
        expr t   = whnf(infer(e));
        return t == mk_Prop();
    } else {
        return false;
    }
}

bool type_inference::is_def_eq_binding(expr e1, expr e2) {
    lean_assert(e1.kind() == e2.kind());
    lean_assert(is_binding(e1));
    expr_kind k = e1.kind();
    buffer<expr> subst;
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
            subst.push_back(mk_tmp_local(*var_e1_type));
        } else {
            expr const & dont_care = mk_Prop();
            subst.push_back(dont_care);
        }
        e1 = binding_body(e1);
        e2 = binding_body(e2);
    } while (e1.kind() == k && e2.kind() == k);
    return is_def_eq_core(instantiate_rev(e1, subst.size(), subst.data()),
                          instantiate_rev(e2, subst.size(), subst.data()));
}

bool type_inference::is_def_eq_args(expr const & e1, expr const & e2) {
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

bool type_inference::is_def_eq_eta(expr const & e1, expr const & e2) {
    expr new_e1 = try_eta(e1);
    expr new_e2 = try_eta(e2);
    if (e1 != new_e1 || e2 != new_e2) {
        scope s(*this);
        if (is_def_eq_core(new_e1, new_e2)) {
            s.commit();
            return true;
        }
    }
    return false;
}

bool type_inference::is_def_eq_proof_irrel(expr const & e1, expr const & e2) {
    if (!m_env.prop_proof_irrel())
        return false;
    expr e1_type = infer(e1);
    expr e2_type = infer(e2);
    if (is_prop(e1_type)) {
        scope s(*this);
        if (is_def_eq_core(e1_type, e2_type)) {
            s.commit();
            return true;
        }
    }
    return false;
}

/** \brief Given \c ma of the form <tt>?m t_1 ... t_n</tt>, (try to) assign
    ?m to (an abstraction of) v. Return true if success and false otherwise. */
bool type_inference::assign_mvar(expr const & ma, expr const & v) {
    buffer<expr> args;
    expr const & m = get_app_args(ma, args);
    buffer<expr> locals;
    for (expr const & arg : args) {
        if (!is_tmp_local(arg))
            break; // is not local
        if (std::any_of(locals.begin(), locals.end(), [&](expr const & local) {
                    return mlocal_name(local) == mlocal_name(arg); }))
            break; // duplicate local
        locals.push_back(arg);
    }
    lean_assert(is_mvar(m));
    expr new_v = instantiate_uvars_mvars(v);

    if (!validate_assignment(m, locals, v))
        return false;

    if (args.empty()) {
        // easy case
        update_assignment(m, new_v);
        return true;
    } else if (args.size() == locals.size()) {
        update_assignment(m, Fun(locals, new_v));
        return true;
    } else {
        // This case is imprecise since it is not a higher order pattern.
        // That the term \c ma is of the form (?m t_1 ... t_n) and the t_i's are not pairwise
        // distinct local constants.
        expr m_type = infer_metavar(m);
        for (unsigned i = 0; i < args.size(); i++) {
            m_type = whnf(m_type);
            if (!is_pi(m_type))
                return false;
            lean_assert(i <= locals.size());
            if (i == locals.size())
                locals.push_back(mk_tmp_local(binding_domain(m_type)));
            lean_assert(i < locals.size());
            m_type = instantiate(binding_body(m_type), locals[i]);
        }
        lean_assert(locals.size() == args.size());
        update_assignment(m, Fun(locals, new_v));
        return true;
    }
}

/** \brief This is an auxiliary method for is_def_eq. It handles the "easy cases". */
lbool type_inference::quick_is_def_eq(expr const & e1, expr const & e2) {
    if (e1 == e2)
        return l_true;

    expr const & f1 = get_app_fn(e1);
    if (is_mvar(f1)) {
        if (is_assigned(f1)) {
            return to_lbool(is_def_eq_core(subst_mvar(e1), e2));
        } else {
            return to_lbool(assign_mvar(e1, e2));
        }
    }

    expr const & f2 = get_app_fn(e2);
    if (is_mvar(f2)) {
        if (is_assigned(f2)) {
            return to_lbool(is_def_eq_core(e1, subst_mvar(e2)));
        } else {
            return to_lbool(assign_mvar(e2, e1));
        }
    }

    if (e1.kind() == e2.kind()) {
        switch (e1.kind()) {
        case expr_kind::Lambda: case expr_kind::Pi:
            return to_lbool(is_def_eq_binding(e1, e2));
        case expr_kind::Sort:
            return to_lbool(is_def_eq(sort_level(e1), sort_level(e2)));
        case expr_kind::Meta:  case expr_kind::Var:
        case expr_kind::Local: case expr_kind::App:
        case expr_kind::Constant: case expr_kind::Macro:
            // We do not handle these cases in this method.
            break;
        }
    }
    return l_undef; // This is not an "easy case"
}

auto type_inference::lazy_delta_reduction_step(expr & t_n, expr & s_n) -> reduction_status {
    auto d_t = is_delta(t_n);
    auto d_s = is_delta(s_n);
    if (!d_t && !d_s) {
        return reduction_status::DefUnknown;
    } else if (d_t && !d_s) {
        t_n = whnf_core(unfold_names(t_n, 0));
    } else if (!d_t && d_s) {
        s_n = whnf_core(unfold_names(s_n, 0));
    } else if (d_t->get_height() > d_s->get_height()) {
        t_n = whnf_core(unfold_names(t_n, d_s->get_height() + 1));
    } else if (d_t->get_height() < d_s->get_height()) {
        s_n = whnf_core(unfold_names(s_n, d_t->get_height() + 1));
    } else {
        if (is_app(t_n) && is_app(s_n) && is_eqp(*d_t, *d_s)) {
            if (!is_opaque(*d_t)) {
                scope s(*this);
                if (is_def_eq_args(t_n, s_n) &&
                    is_def_eq(const_levels(get_app_fn(t_n)), const_levels(get_app_fn(s_n)))) {
                    s.commit();
                    return reduction_status::DefEqual;
                }
            }
        }
        t_n = whnf_core(unfold_names(t_n, d_t->get_height() - 1));
        s_n = whnf_core(unfold_names(s_n, d_s->get_height() - 1));
    }
    switch (quick_is_def_eq(t_n, s_n)) {
    case l_true:  return reduction_status::DefEqual;
    case l_false: return reduction_status::DefDiff;
    case l_undef: return reduction_status::Continue;
    }
    lean_unreachable();
}

lbool type_inference::lazy_delta_reduction(expr & t_n, expr & s_n) {
    while (true) {
        switch (lazy_delta_reduction_step(t_n, s_n)) {
        case reduction_status::Continue:   break;
        case reduction_status::DefUnknown: return l_undef;
        case reduction_status::DefEqual:   return l_true;
        case reduction_status::DefDiff:    return l_false;
        }
    }
}

auto type_inference::ext_reduction_step(expr & t_n, expr & s_n) -> reduction_status {
    auto new_t_n = norm_ext(t_n);
    auto new_s_n = norm_ext(s_n);
    if (!new_t_n && !new_s_n)
        return reduction_status::DefUnknown;
    if (new_t_n)
        t_n = whnf_core(*new_t_n);
    if (new_s_n)
        s_n = whnf_core(*new_s_n);
    switch (quick_is_def_eq(t_n, s_n)) {
    case l_true:  return reduction_status::DefEqual;
    case l_false: return reduction_status::DefDiff;
    case l_undef: return reduction_status::Continue;
    }
    lean_unreachable();
}

// Apply lazy delta-reduction and then normalizer extensions
lbool type_inference::reduce_def_eq(expr & t_n, expr & s_n) {
    while (true) {
        // first, keep applying lazy delta-reduction while applicable
        lbool r = lazy_delta_reduction(t_n, s_n);
        if (r != l_undef) return r;

        // try normalizer extensions
        switch (ext_reduction_step(t_n, s_n)) {
        case reduction_status::Continue:   break;
        case reduction_status::DefUnknown: return l_undef;
        case reduction_status::DefEqual:   return l_true;
        case reduction_status::DefDiff:    return l_false;
        }
    }
}

bool type_inference::is_def_eq_core(expr const & t, expr const & s) {
    check_system("is_definitionally_equal");
    lbool r = quick_is_def_eq(t, s);
    if (r != l_undef) return r == l_true;

    expr t_n = whnf_core(t);
    expr s_n = whnf_core(s);

    if (!is_eqp(t_n, t) || !is_eqp(s_n, s)) {
        r = quick_is_def_eq(t_n, s_n);
        if (r != l_undef) return r == l_true;
    }

    r = reduce_def_eq(t_n, s_n);
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

    if (is_def_eq_proof_irrel(t_n, s_n))
        return true;

    if (on_is_def_eq_failure(t_n, s_n))
        return is_def_eq_core(t_n, s_n);
    else
        return false;
}

bool type_inference::is_def_eq(expr const & e1, expr const & e2) {
    scope s(*this);
    if (is_def_eq_core(e1, e2)) {
        s.commit();
        return true;
    }
    return false;
}

expr type_inference::infer_constant(expr const & e) {
    declaration d    = m_env.get(const_name(e));
    auto const & ps = d.get_univ_params();
    auto const & ls = const_levels(e);
    if (length(ps) != length(ls))
        throw exception("infer type failed, incorrect number of universe levels");
    return instantiate_type_univ_params(d, ls);
}

expr type_inference::infer_macro(expr const & e) {
    auto def = macro_def(e);
    bool infer_only = true;
    // Remark: we are ignoring constraints generated by the macro definition.
    return def.check_type(e, *m_ext_ctx, infer_only).first;
}

expr type_inference::infer_lambda(expr e) {
    buffer<expr> es, ds, ls;
    while (is_lambda(e)) {
        es.push_back(e);
        ds.push_back(binding_domain(e));
        expr d = instantiate_rev(binding_domain(e), ls.size(), ls.data());
        expr l = mk_tmp_local(d, binding_info(e));
        ls.push_back(l);
        e = binding_body(e);
    }
    expr t = infer(instantiate_rev(e, ls.size(), ls.data()));
    expr r = abstract_locals(t, ls.size(), ls.data());
    unsigned i = es.size();
    while (i > 0) {
        --i;
        r = mk_pi(binding_name(es[i]), ds[i], r, binding_info(es[i]));
    }
    return r;
}

/** \brief Make sure \c e is a sort, if it is not throw an exception using \c ref as a reference */
void type_inference::ensure_sort(expr const & e, expr const & /* ref */) {
    // Remark: for simplicity reasons, we just fail if \c e is not a sort.
    if (!is_sort(e))
        throw exception("infer type failed, sort expected");
}

expr type_inference::infer_pi(expr const & e0) {
    buffer<expr>  ls;
    buffer<level> us;
    expr e = e0;
    while (is_pi(e)) {
        expr d      = instantiate_rev(binding_domain(e), ls.size(), ls.data());
        expr d_type = whnf(infer(d));
        ensure_sort(d_type, e0);
        us.push_back(sort_level(d_type));
        expr l  = mk_tmp_local(d, binding_info(e));
        ls.push_back(l);
        e = binding_body(e);
    }
    e = instantiate_rev(e, ls.size(), ls.data());
    expr e_type = whnf(infer(e));
    ensure_sort(e_type, e0);
    level r = sort_level(e_type);
    unsigned i = ls.size();
    bool imp = m_env.impredicative();
    while (i > 0) {
        --i;
        r = imp ? mk_imax(us[i], r) : mk_max(us[i], r);
    }
    return mk_sort(r);
}

/** \brief Make sure \c e is a Pi-expression, if it is not throw an exception using \c ref as a reference */
void type_inference::ensure_pi(expr const & e, expr const & /* ref */) {
    // Remark: for simplicity reasons, we just fail if \c e is not a Pi.
    if (!is_pi(e))
        throw exception("infer type failed, Pi expected");
    // Potential problem: e is of the form (f ...) where f is a constant that is not marked as reducible.
    // So, whnf does not reduce it, and we fail to detect that e is can be reduced to a Pi-expression.
}

expr type_inference::infer_app(expr const & e) {
    buffer<expr> args;
    expr const & f = get_app_args(e, args);
    expr f_type = infer(f);
    unsigned j        = 0;
    unsigned nargs    = args.size();
    for (unsigned i = 0; i < nargs; i++) {
        if (is_pi(f_type)) {
            f_type = binding_body(f_type);
        } else {
            f_type = whnf(instantiate_rev(f_type, i-j, args.data()+j));
            ensure_pi(f_type, e);
            f_type = binding_body(f_type);
            j = i;
        }
    }
    return instantiate_rev(f_type, nargs-j, args.data()+j);
}

expr type_inference::infer(expr const & e) {
    lean_assert(!is_var(e));
    lean_assert(closed(e));
    check_system("infer_type");

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
    }
    // TODO(Leo): cache results if we have performance problems
    return r;
}

void type_inference::clear_cache() {
}

void initialize_type_inference() {
    g_prefix = new name(name::mk_internal_unique_name());
}

void finalize_type_inference() {
    delete g_prefix;
}
}
